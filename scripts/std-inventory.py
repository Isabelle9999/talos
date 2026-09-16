#!/usr/bin/env python3
"""
std-inventory.py

Reads every programs/rust/build/<crate>/program.wat, computes three body hashes
per function (exact / mod-call / mod-call+const), optionally recovers Rust symbol
names from unstripped artifacts via wasm-tools, and writes docs/std_inventory.md.

No third-party packages: Python 3.8+ stdlib only.
"""

import hashlib
import re
import shutil
import subprocess
import sys
from collections import defaultdict
from pathlib import Path


# ── Wasm binary: code-section body sizes ─────────────────────────────────────

def _leb128_u(data: bytes, pos: int) -> tuple:
    result, shift = 0, 0
    while pos < len(data):
        b = data[pos]; pos += 1
        result |= (b & 0x7F) << shift
        shift += 7
        if not (b & 0x80):
            break
    return result, pos


def code_sizes(wasm_path: Path):
    """Return per-local-function body byte sizes from the binary code section, or None."""
    try:
        data = wasm_path.read_bytes()
    except OSError:
        return None
    if data[:4] != b'\x00asm':
        return None
    pos = 8
    while pos < len(data):
        sec_id = data[pos]; pos += 1
        sec_size, pos = _leb128_u(data, pos)
        if sec_id == 10:                      # Code section
            count, cur = _leb128_u(data, pos)
            sizes = []
            for _ in range(count):
                bsz, cur = _leb128_u(data, cur)
                sizes.append(bsz)
                cur += bsz
            return sizes
        pos += sec_size
    return None


# ── WAT parsing ───────────────────────────────────────────────────────────────

def parse_type_table(wat: str) -> dict:
    """Return {type_index: "(p1 p2)->(r1)"} for every (type ...) declaration."""
    sigs = {}
    for line in wat.splitlines():
        m = re.match(r'\s*\(type \(;(\d+);\) \(func(.*)\)\)\s*$', line)
        if not m:
            continue
        idx = int(m.group(1))
        inner = m.group(2)          # everything between '(func' and the last '))'
        params = []
        for pm in re.finditer(r'\(param ([^)]+)\)', inner):
            params.extend(pm.group(1).split())
        results = []
        rm = re.search(r'\(result ([^)]+)\)', inner)
        if rm:
            results.extend(rm.group(1).split())
        sigs[idx] = f"({' '.join(params)})->({' '.join(results)})"
    return sigs


def parse_func_type_map(wat: str) -> dict:
    """Return {abs_func_index: type_index} for imports and local functions."""
    ft = {}
    # Handles both stripped  '(func (;N;) (type T) ...'
    # and unstripped         '(func $name (;N;) (type T) ...'
    for m in re.finditer(r'\(func(?:\s+\$\S+)?\s+\(;(\d+);\)\s+\(type\s+(\d+)\)', wat):
        ft[int(m.group(1))] = int(m.group(2))
    return ft


def count_import_funcs(wat: str) -> int:
    return len(re.findall(r'\(import [^(]+\(func\b', wat))


def split_function_blocks(wat: str) -> list:
    """Return [(abs_index, lines)] for every top-level (func (;N;) …) block."""
    lines = wat.splitlines()
    out = []
    i = 0
    while i < len(lines):
        stripped = lines[i].lstrip()
        if not stripped.startswith('(func (;'):
            i += 1
            continue
        m = re.match(r'\(func \(;(\d+);\)', stripped)
        if not m:
            i += 1
            continue
        abs_idx = int(m.group(1))
        depth, block = 0, []
        while i < len(lines):
            l = lines[i]
            code = l.split(';;')[0]      # strip line comments before counting
            depth += code.count('(') - code.count(')')
            block.append(l)
            i += 1
            if depth <= 0:
                break
        out.append((abs_idx, block))
    return out


def extract_body(func_lines: list) -> str:
    """Body text: all lines after the header, before the closing paren, normalised."""
    if len(func_lines) <= 1:
        return ''
    body = list(func_lines[1:])
    while body and body[-1].strip() in (')', ''):
        body.pop()
    return '\n'.join(l.strip() for l in body if l.strip())


# ── Hash computation ──────────────────────────────────────────────────────────

_CALL = re.compile(r'(?<![_\w])call (\d+)')
_I32C = re.compile(r'\bi32\.const -?\d+\b')


def _sha12(s: str) -> str:
    return hashlib.sha256(s.encode()).hexdigest()[:12]


def compute_hashes(body: str, type_sigs: dict, func_types: dict) -> tuple:
    """Return (h_exact, h_mod_call, h_mod_call_const)."""
    h_e = _sha12(body)

    def repl_call(line: str) -> str:
        def sub(m):
            k = int(m.group(1))
            t = func_types.get(k)
            if t is not None and t in type_sigs:
                return f'call @{type_sigs[t]}'
            return m.group(0)
        return _CALL.sub(sub, line)

    mod_call_lines = [repl_call(l) for l in body.splitlines()]
    mod_call = '\n'.join(mod_call_lines)
    h_c = _sha12(mod_call)

    h_cc = _sha12('\n'.join(_I32C.sub('i32.const _', l) for l in mod_call_lines))
    return h_e, h_c, h_cc


# ── Symbol recovery ───────────────────────────────────────────────────────────

_RUST_ENC = {
    '$LT$': '<', '$GT$': '>', '$u20$': ' ', '$C$': ',',
    '$RF$': '&', '$BP$': '*', '$u5b$': '[', '$u5d$': ']',
    '$u7b$': '{', '$u7d$': '}', '$u3b$': ';', '$u27$': "'",
    '$u2b$': '+',
}


def _decode_ident(s: str) -> str:
    for k, v in _RUST_ENC.items():
        s = s.replace(k, v)
    return s.replace('..', '::')


def demangle(sym: str) -> str:
    """Demangle a Rust symbol: full decode for _ZN…E, raw for everything else."""
    if not (sym.startswith('_ZN') and sym.endswith('E')):
        return sym
    inner = sym[3:-1]
    parts = []
    i = 0
    while i < len(inner):
        j = i
        while j < len(inner) and inner[j].isdigit():
            j += 1
        if j == i:
            break
        n = int(inner[i:j])
        end = j + n
        if end > len(inner):
            break
        name = _decode_ident(inner[j:end])
        if not parts and name.startswith('_'):
            name = name[1:]          # strip leading '_' from impl-block segments
        parts.append(name)
        i = end
    # Drop trailing Rust hash segment: starts with 'h' followed only by hex digits
    if parts and re.match(r'^h[0-9a-f]+$', parts[-1], re.IGNORECASE):
        parts.pop()
    return '::'.join(parts) if parts else sym


def get_symbol_map(unstripped: Path, wasm_tools: str) -> dict:
    """Return {local_func_index: demangled_name} from the unstripped binary."""
    try:
        proc = subprocess.run(
            [wasm_tools, 'print', str(unstripped)],
            capture_output=True, text=True, check=True, timeout=30,
        )
    except Exception:
        return {}
    wat = proc.stdout
    import_count = count_import_funcs(wat)
    result = {}
    for m in re.finditer(r'\(func (\$\S+) \(;(\d+);\)', wat):
        raw = m.group(1)[1:]          # strip '$'
        local = int(m.group(2)) - import_count
        if local >= 0:
            result[local] = demangle(raw)
    return result


# ── Cargo.toml opt-level ──────────────────────────────────────────────────────

def parse_opt_levels(cargo_toml: Path) -> tuple:
    """Return (default_opt: int, {normalised_pkg: opt_level})."""
    default_opt = 0
    pkg_opts: dict = {}
    section = ''
    for line in cargo_toml.read_text(encoding='utf-8').splitlines():
        line = line.strip()
        if line.startswith('[') and line.endswith(']'):
            section = line[1:-1]
        elif '=' in line:
            k, _, v = line.partition('=')
            k, v = k.strip(), v.strip().strip('"')
            if k == 'opt-level':
                if section == 'profile.release':
                    try: default_opt = int(v)
                    except ValueError: pass
                elif section.startswith('profile.release.package.'):
                    pkg = section[len('profile.release.package.'):].replace('-', '_')
                    try: pkg_opts[pkg] = int(v)
                    except ValueError: pass
    return default_opt, pkg_opts


def resolve_opt(crate: str, default_opt: int, pkg_opts: dict) -> int:
    return pkg_opts.get(crate.replace('-', '_'), default_opt)


# ── Markdown helpers ──────────────────────────────────────────────────────────

def trunc(s: str, n: int) -> str:
    return s if len(s) <= n else s[:n - 1] + '…'


def md_row(*cells) -> str:
    return '| ' + ' | '.join(str(c) for c in cells) + ' |'


# ── Main ──────────────────────────────────────────────────────────────────────

def main() -> None:
    repo       = Path(__file__).resolve().parent.parent
    build_root = repo / 'programs' / 'rust' / 'build'
    target_dir = repo / 'programs' / 'rust' / 'target' / 'wasm32-unknown-unknown' / 'release'
    cargo_toml = repo / 'programs' / 'rust' / 'Cargo.toml'
    out_path   = repo / 'docs' / 'std_inventory.md'

    wasm_tools: str = shutil.which('wasm-tools') or ''
    default_opt, pkg_opts = parse_opt_levels(cargo_toml)

    all_funcs: list = []
    any_inst_fallback = False
    sym_diag: list = []          # (crate, artifact_found, n_symbols) for header

    for wat_path in sorted(build_root.glob('*/program.wat')):
        crate = wat_path.parent.name
        wat   = wat_path.read_text(encoding='utf-8')
        wasm  = wat_path.parent / 'program.wasm'

        type_sigs  = parse_type_table(wat)
        func_types = parse_func_type_map(wat)
        n_imports  = count_import_funcs(wat)
        opt        = resolve_opt(crate, default_opt, pkg_opts)
        csizes     = code_sizes(wasm)

        sym_map: dict = {}
        if wasm_tools:
            for cand in (crate, crate.replace('_', '-')):
                p = target_dir / f'{cand}.wasm'
                if p.exists():
                    sym_map = get_symbol_map(p, wasm_tools)
                    sym_diag.append((crate, True, len(sym_map)))
                    break
            else:
                sym_diag.append((crate, False, 0))

        for abs_idx, block in split_function_blocks(wat):
            local = abs_idx - n_imports
            body  = extract_body(block)
            h_e, h_c, h_cc = compute_hashes(body, type_sigs, func_types)

            if csizes is not None and 0 <= local < len(csizes):
                size      = csizes[local]
                size_note = 'bin'
            else:
                size      = sum(1 for l in body.splitlines() if l)
                size_note = 'inst'
                any_inst_fallback = True

            all_funcs.append({
                'crate':     crate,
                'abs':       abs_idx,
                'local':     local,
                'opt':       opt,
                'symbol':    sym_map.get(local, ''),
                'h_e':       h_e,
                'h_c':       h_c,
                'h_cc':      h_cc,
                'size':      size,
                'size_note': size_note,
            })

    if not all_funcs:
        sys.exit('No WAT files found under programs/rust/build/.')

    # ── Equivalence summary ───────────────────────────────────────────────────

    def equiv_stats(key: str) -> tuple:
        cls: dict = defaultdict(list)
        for f in all_funcs:
            cls[f[key]].append(f)
        distinct = len(cls)
        in_dups  = sum(len(v) for v in cls.values() if len(v) >= 2)
        return distinct, in_dups

    e_d,  e_dup  = equiv_stats('h_e')
    c_d,  c_dup  = equiv_stats('h_c')
    cc_d, cc_dup = equiv_stats('h_cc')
    total  = len(all_funcs)
    n_crates = len({f['crate'] for f in all_funcs})

    # ── Per modulo-call class ─────────────────────────────────────────────────

    call_cls: dict = defaultdict(list)
    for f in all_funcs:
        call_cls[f['h_c']].append(f)

    class_rows = []
    for h, members in call_cls.items():
        members = sorted(members, key=lambda m: (m['crate'], m['local']))
        rep     = members[0]
        n_crate = len({m['crate'] for m in members})
        insts   = ', '.join(f"{m['crate']}:{m['local']}" for m in members)
        symbol = next((m['symbol'] for m in members if m['symbol']), '')
        class_rows.append({
            'hash':    h,
            'symbol':  symbol,
            'opt':     rep['opt'],
            'n_crate': n_crate,
            'insts':   insts,
            'size':    rep['size'],
        })
    class_rows.sort(key=lambda r: (-r['n_crate'], -r['size']))

    # ── Build markdown ────────────────────────────────────────────────────────

    size_label = 'inst count' if any_inst_fallback else 'code bytes (bin)'

    doc = [
        '# Standard Function Inventory',
        '',
        f'Crates: {n_crates}  —  Functions: {total}',
        '',
    ]
    if wasm_tools:
        found_crates  = [(c, n) for c, ok, n in sym_diag if ok]
        missing_crates = [c for c, ok, _ in sym_diag if not ok]
        doc.append(
            'Symbols: recovered via `wasm-tools print` on unstripped artifacts '
            '(`programs/rust/target/…/release/*.wasm`).'
        )
        if found_crates:
            doc.append(
                'Artifacts found: '
                + ', '.join(f'{c} ({n})' for c, n in found_crates) + '.'
            )
        if missing_crates:
            doc.append(
                'No unstripped artifact for: '
                + ', '.join(missing_crates)
                + ' — symbol column empty for those crates.'
            )
    else:
        print('WARNING: wasm-tools not found on PATH — symbol column will be empty.',
              file=sys.stderr)
        doc.append('Symbols: `wasm-tools` not found on PATH — symbol column empty.')
    doc.append(f'Size column: {size_label}.')
    doc += [
        '',
        '## Equivalence summary',
        '',
        f'Total functions across all crates: {total}',
        '',
        '| Equivalence | Distinct classes | Functions in duplicate groups |',
        '| --- | ---: | ---: |',
        f'| exact | {e_d} | {e_dup} |',
        f'| mod-call | {c_d} | {c_dup} |',
        f'| mod-call+const | {cc_d} | {cc_dup} |',
        '',
        '## Modulo-call equivalence classes',
        '',
        'One row per class; sorted by crate count desc, then size desc.',
        f'Symbol: first occurrence (demangled _ZN…E; raw for _R…).  Size: {size_label}.',
        '',
        '| Symbol | Opt | Class hash | Crates | Instances | Size |',
        '| --- | ---: | --- | ---: | --- | ---: |',
    ]
    for r in class_rows:
        doc.append(md_row(
            trunc(r['symbol'], 60),
            r['opt'],
            f'`{r["hash"]}`',
            r['n_crate'],
            trunc(r['insts'], 110),
            r['size'],
        ))
    doc.append('')

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text('\n'.join(doc), encoding='utf-8')
    print(f'Wrote {out_path.relative_to(repo)}')

    # ── Print summary table to stdout ─────────────────────────────────────────
    print()
    print(f'Crates: {n_crates}  Functions: {total}')
    print()
    print('| Equivalence    | Distinct classes | In duplicate groups |')
    print('| ---            |             ---: |                ---: |')
    print(f'| exact          |             {e_d:4} |                {e_dup:4} |')
    print(f'| mod-call       |             {c_d:4} |                {c_dup:4} |')
    print(f'| mod-call+const |             {cc_d:4} |                {cc_dup:4} |')


if __name__ == '__main__':
    main()
