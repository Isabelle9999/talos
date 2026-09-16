# Standard Function Inventory

Crates: 18  —  Functions: 624

Symbols: recovered via `wasm-tools print` on unstripped artifacts (`programs/rust/target/…/release/*.wasm`).
Artifacts found: float_minmax (68), float_reinterpret (12), float_round (7), float_trunc (55), mergesort (120), num_integer (3), num_integer_opt3 (1), quicksort (71), rust_array (6), rust_array_tests (9), rust_u64 (68), rust_u64_tests (76), swap_elements (62), swap_elements_opt3 (58), total_variation (2).
No unstripped artifact for: byte_echo, gcd_stdio, hex_stdio, xor — symbol column empty for those crates.
Size column: code bytes (bin).

## Equivalence summary

Total functions across all crates: 624

| Equivalence | Distinct classes | Functions in duplicate groups |
| --- | ---: | ---: |
| exact | 524 | 141 |
| mod-call | 354 | 319 |
| mod-call+const | 287 | 399 |

## Modulo-call equivalence classes

One row per class; sorted by crate count desc, then size desc.
Symbol: first occurrence (demangled _ZN…E; raw for _R…).  Size: code bytes (bin).

| Symbol | Opt | Class hash | Crates | Instances | Size |
| --- | ---: | --- | ---: | --- | ---: |
| _RNvNtCsebHcaeoSrxy_3std5alloc8rust_oom | 3 | `51821617ff5a` | 11 | byte_echo:11, float_minmax:37, float_trunc:31, gcd_stdio:13, hex_stdio:35, mergesort:28, rust_u64:42, rust_u6… | 47 |
| _RNvCsfLfy6EI15iL_7___rustc26___rust_alloc_error_handler | 3 | `8d00482976f4` | 11 | byte_echo:10, byte_echo:12, float_minmax:36, float_minmax:55, float_trunc:30, float_trunc:49, gcd_stdio:12, g… | 13 |
| _RINvNtNtCsebHcaeoSrxy_3std3sys9backtrace26___rust_end_shor… | 3 | `9b3dc4f30cda` | 11 | byte_echo:7, float_minmax:18, float_minmax:20, float_trunc:12, float_trunc:14, gcd_stdio:9, hex_stdio:24, hex… | 11 |
| _RNvCsfLfy6EI15iL_7___rustc18___rust_start_panic | 3 | `99737c82ba99` | 11 | byte_echo:3, float_minmax:13, float_trunc:7, gcd_stdio:4, hex_stdio:13, hex_stdio:19, mergesort:6, mergesort:… | 9 |
| _RNvCsfLfy6EI15iL_7___rustc35___rust_no_alloc_shim_is_unsta… | 3 | `7187f0675eb3` | 11 | byte_echo:1, float_minmax:12, float_trunc:6, gcd_stdio:3, hex_stdio:11, mergesort:4, rust_u64:17, rust_u64_te… | 3 |
| _RNvXsZ_NtCs5cOc02OMXlo_5alloc6stringNtB5_6StringNtNtCsgXGp… | 0 | `2a507e29c80a` | 8 | float_minmax:47, float_trunc:41, hex_stdio:49, mergesort:37, rust_u64:52, rust_u64_tests:60, swap_elements:43… | 297 |
| _RNvMs4_NtCs5cOc02OMXlo_5alloc7raw_vecNtB5_11RawVecInner11f… | 0 | `15af7d960b39` | 8 | float_minmax:22, float_trunc:16, hex_stdio:28, mergesort:0, mergesort:21, rust_u64:27, rust_u64_tests:35, swa… | 182 |
| _RINvNvMs2_NtCs5cOc02OMXlo_5alloc7raw_vecINtB8_11RawVecInne… | 0 | `94caaa362126` | 8 | float_minmax:14, float_trunc:8, hex_stdio:20, mergesort:1, mergesort:13, rust_u64:19, rust_u64_tests:27, swap… | 173 |
| _RNvXsZ_NtCs5cOc02OMXlo_5alloc6stringNtB5_6StringNtNtCsgXGp… | 0 | `8561fc3d2a8b` | 8 | float_minmax:48, float_trunc:42, hex_stdio:50, mergesort:38, rust_u64:53, rust_u64_tests:61, swap_elements:44… | 94 |
| _RNvXs0_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB5… | 0 | `94e0b294642a` | 8 | float_minmax:42, float_trunc:36, hex_stdio:41, mergesort:32, rust_u64:47, rust_u64_tests:55, swap_elements:38… | 72 |
| _RNvNtCsgXGp5Oqx2Ny_4core9panicking9panic_fmt | 0 | `e3891b5aae3b` | 8 | float_minmax:58, float_trunc:52, hex_stdio:64, mergesort:47, rust_u64:63, rust_u64_tests:71, swap_elements:54… | 71 |
| _RNvCsfLfy6EI15iL_7___rustc17rust_begin_unwind | 0 | `278fd7eecba8` | 8 | float_minmax:35, float_trunc:29, hex_stdio:33, mergesort:26, rust_u64:40, rust_u64_tests:48, swap_elements:31… | 56 |
| _RINvNtCsgXGp5Oqx2Ny_4core3ptr13drop_in_placeINtNtB4_6optio… | 0 | `d1c1f4a48277` | 8 | float_minmax:15, float_trunc:9, hex_stdio:21, mergesort:14, rust_u64:20, rust_u64_tests:28, swap_elements:11,… | 35 |
| _RINvNtCsgXGp5Oqx2Ny_4core3ptr13drop_in_placeNtNvNtCsebHcae… | 0 | `ce8bcc48d830` | 8 | float_minmax:17, float_trunc:11, hex_stdio:23, mergesort:16, rust_u64:22, rust_u64_tests:30, swap_elements:13… | 34 |
| _RINvNtCsgXGp5Oqx2Ny_4core3ptr13drop_in_placeNtNtCs5cOc02OM… | 0 | `022bf026098a` | 8 | float_minmax:16, float_trunc:10, hex_stdio:22, mergesort:15, rust_u64:21, rust_u64_tests:29, swap_elements:12… | 32 |
| _RNvNtCs5cOc02OMXlo_5alloc7raw_vec12handle_error | 0 | `71675ea398ad` | 8 | float_minmax:54, float_trunc:48, hex_stdio:57, mergesort:43, rust_u64:59, rust_u64_tests:67, swap_elements:50… | 28 |
| _RNvXs2_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB5… | 0 | `24429dcb603f` | 8 | float_minmax:46, float_trunc:40, hex_stdio:47, hex_stdio:65, mergesort:36, rust_u64:51, rust_u64_tests:59, sw… | 20 |
| _RNvCsfLfy6EI15iL_7___rustc10rust_panic | 0 | `f2edbb8d3ad8` | 8 | float_minmax:25, float_trunc:19, hex_stdio:31, mergesort:24, rust_u64:30, rust_u64_tests:38, swap_elements:21… | 14 |
| _RNvXs1_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB5… | 0 | `b586c27f6e37` | 8 | float_minmax:44, float_trunc:38, hex_stdio:43, mergesort:34, rust_u64:49, rust_u64_tests:57, swap_elements:40… | 12 |
| _RNvYINtNvNtCsebHcaeoSrxy_3std9panicking11begin_panic7Paylo… | 0 | `1801c84fed3b` | 8 | float_minmax:51, float_trunc:45, hex_stdio:55, mergesort:41, rust_u64:56, rust_u64_tests:64, swap_elements:47… | 9 |
| _RNvCsfLfy6EI15iL_7___rustc12___rust_abort | 0 | `5e6017027437` | 8 | float_minmax:29, float_trunc:23, hex_stdio:32, mergesort:25, rust_u64:34, rust_u64_tests:42, swap_elements:25… | 3 |
| _RNvNtCsgXGp5Oqx2Ny_4core3fmt5write | 0 | `ac867edd5d8e` | 7 | float_minmax:59, float_trunc:53, mergesort:48, rust_u64:64, rust_u64_tests:72, swap_elements:55, swap_element… | 628 |
| _RNvMsa_NtCsgXGp5Oqx2Ny_4core3fmtNtB5_9Formatter9write_str | 0 | `a94e992fbfa1` | 7 | float_minmax:64, float_trunc:54, mergesort:53, rust_u64:65, rust_u64_tests:73, swap_elements:60, swap_element… | 30 |
| _RNvNtCsgXGp5Oqx2Ny_4core9panicking5panic | 0 | `d0208b2654ec` | 7 | float_minmax:57, float_trunc:51, hex_stdio:62, rust_u64:62, rust_u64_tests:70, swap_elements:53, swap_element… | 21 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 0 | `51089a058783` | 6 | float_minmax:27, float_trunc:21, rust_u64:32, rust_u64_tests:40, swap_elements:23, swap_elements_opt3:19 | 379 |
| _RNvXs_NtCsjqx8TIyZbP9_8dlmalloc3sysNtB4_6SystemNtB6_9Alloc… | 0 | `3e68f16e21d1` | 6 | float_minmax:53, float_trunc:47, rust_u64:58, rust_u64_tests:66, swap_elements:49, swap_elements_opt3:45 | 96 |
| _RNvCsfLfy6EI15iL_7___rustc11___rdl_alloc | 0 | `ccd660722d00` | 6 | float_minmax:26, float_trunc:20, rust_u64:31, rust_u64_tests:39, swap_elements:22, swap_elements_opt3:18 | 31 |
| _RNvCsfLfy6EI15iL_7___rustc14___rust_realloc | 0 | `b00900ae0087` | 6 | float_minmax:11, float_trunc:5, rust_u64:16, rust_u64_tests:24, swap_elements:7, swap_elements_opt3:3 | 17 |
| _RNvCsfLfy6EI15iL_7___rustc14___rust_dealloc | 0 | `dfffcbc2b1ee` | 6 | float_minmax:10, float_trunc:4, rust_u64:15, rust_u64_tests:23, swap_elements:6, swap_elements_opt3:2 | 15 |
| _RNvCsfLfy6EI15iL_7___rustc12___rust_alloc | 0 | `b241a4413bd7` | 6 | float_minmax:9, float_trunc:3, rust_u64:14, rust_u64_tests:22, swap_elements:5, swap_elements_opt3:1 | 13 |
| _RNvNtNtCsgXGp5Oqx2Ny_4core3str5count14do_count_chars | 0 | `635603682570` | 5 | float_minmax:62, hex_stdio:79, mergesort:51, swap_elements:58, swap_elements_opt3:54 | 875 |
| core::fmt::Write::write_fmt | 3 | `e3b0c44298fc` | 5 | byte_echo:4, gcd_stdio:5, hex_stdio:14, mergesort:7, xor:5 | 2 |
| _RNvMsa_NtCsgXGp5Oqx2Ny_4core3fmtNtB5_9Formatter12pad_integ… | 0 | `cd55aae3023a` | 4 | float_minmax:61, mergesort:50, swap_elements:57, swap_elements_opt3:53 | 796 |
| _RNvNvMsa_NtCsgXGp5Oqx2Ny_4core3fmtNtB7_9Formatter12pad_int… | 0 | `1b77b5429129` | 4 | float_minmax:63, mergesort:52, swap_elements:59, swap_elements_opt3:55 | 73 |
| alloc::raw_vec::RawVecInner<A>::finish_grow | 3 | `97ffb547dcc5` | 4 | byte_echo:5, gcd_stdio:7, mergesort:10, xor:6 | 12 |
| alloc::raw_vec::RawVecInner<A>::reserve::do_reserve_and_han… | 3 | `f106e98a543a` | 4 | byte_echo:6, gcd_stdio:8, mergesort:11, xor:7 | 12 |
|  | 3 | `c86abe846e04` | 3 | byte_echo:8, gcd_stdio:10, xor:9 | 44 |
|  | 3 | `4e6606ebdffd` | 3 | byte_echo:9, gcd_stdio:11, xor:10 | 13 |
|  | 3 | `6aee7ba19ff7` | 2 | byte_echo:2, xor:3 | 123 |
| num_integer_opt3::gcd_u64 | 3 | `87ff9fcba583` | 2 | gcd_stdio:1, num_integer_opt3:0 | 115 |
| core::num::_<impl u64>::abs_diff | 0 | `b245b0cff351` | 2 | rust_u64:0, total_variation:0 | 59 |
| len | 0 | `e487d5040e2f` | 2 | rust_array:4, rust_array_tests:5, rust_array_tests:8 | 19 |
| core::slice::raw::from_raw_parts | 0 | `62153ef27002` | 2 | float_minmax:6, swap_elements:3 | 17 |
| gcd_u64 | 0 | `829a5ef710db` | 2 | num_integer:2, rust_u64:1 | 13 |
| float_reinterpret::exports::abs_native | 0 | `ef2a77f7eb57` | 2 | float_reinterpret:0, float_round:4 | 11 |
| core::slice::_<impl [T]>::is_empty | 0 | `5daf875c0ec7` | 2 | rust_array:2, rust_array_tests:3 | 11 |
|  | 3 | `99d78e80b939` | 2 | gcd_stdio:2, xor:1 | 8 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 0 | `0d0b0e7bb092` | 1 | float_minmax:28 | 5099 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 0 | `073ef6f4703d` | 1 | float_trunc:22 | 5099 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 0 | `ec72ad45f8f4` | 1 | rust_u64:33 | 5099 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 0 | `8ec899fd9f15` | 1 | rust_u64_tests:41 | 5099 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 0 | `1dad9bc13b12` | 1 | swap_elements:24 | 5099 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 3 | `46a06c1d5145` | 1 | swap_elements_opt3:20 | 5099 |
|  | 3 | `984e111ffa01` | 1 | hex_stdio:86 | 1622 |
|  | 3 | `bf8cf53b2f9a` | 1 | hex_stdio:7 | 1058 |
|  | 3 | `9df46a822fa1` | 1 | hex_stdio:95 | 970 |
| _RNvCsfLfy6EI15iL_7___rustc13___rdl_realloc | 0 | `71a0432a57f1` | 1 | float_minmax:32 | 949 |
| _RNvCsfLfy6EI15iL_7___rustc13___rdl_realloc | 0 | `88d4163ec086` | 1 | float_trunc:26 | 949 |
| _RNvCsfLfy6EI15iL_7___rustc13___rdl_realloc | 0 | `fc827339c2eb` | 1 | rust_u64:37 | 949 |
| _RNvCsfLfy6EI15iL_7___rustc13___rdl_realloc | 0 | `67e263aef904` | 1 | rust_u64_tests:45 | 949 |
| _RNvCsfLfy6EI15iL_7___rustc13___rdl_realloc | 0 | `e0ea59990a07` | 1 | swap_elements:28 | 949 |
| _RNvCsfLfy6EI15iL_7___rustc13___rdl_realloc | 3 | `1a8a9df805b2` | 1 | swap_elements_opt3:24 | 949 |
|  | 3 | `811835a5ec12` | 1 | hex_stdio:69 | 880 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 0 | `b95486f34ec1` | 1 | float_minmax:31 | 870 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 0 | `e3f496a8dd50` | 1 | float_trunc:25 | 870 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 0 | `9bcc116f919c` | 1 | rust_u64:36 | 870 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 0 | `95ec62214c66` | 1 | rust_u64_tests:44 | 870 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 0 | `0db0401e7951` | 1 | swap_elements:27 | 870 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 3 | `3ecaff4f7e41` | 1 | swap_elements_opt3:23 | 870 |
|  | 3 | `6e0e790509fe` | 1 | hex_stdio:78 | 796 |
| std::io::buffered::bufwriter::BufWriter<W>::flush_buf | 3 | `d44f4c04af59` | 1 | mergesort:3 | 788 |
|  | 3 | `4a31d65c267d` | 1 | hex_stdio:67 | 786 |
|  | 3 | `602162c21e44` | 1 | hex_stdio:82 | 670 |
|  | 3 | `4133ec452353` | 1 | hex_stdio:66 | 628 |
|  | 3 | `4897a984d4bf` | 1 | hex_stdio:71 | 585 |
|  | 3 | `136987403e49` | 1 | hex_stdio:5 | 581 |
|  | 3 | `463479ff6c12` | 1 | hex_stdio:87 | 567 |
| std::io::buffered::bufwriter::BufWriter<W>::write_all_cold | 3 | `1d344b3adb30` | 1 | mergesort:2 | 567 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 0 | `66d5545cb26a` | 1 | float_minmax:34 | 566 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 0 | `6824594f2dae` | 1 | float_trunc:28 | 566 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 0 | `d34967370bb3` | 1 | rust_u64:39 | 566 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 0 | `5c38061f5545` | 1 | rust_u64_tests:47 | 566 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 0 | `bb9cad3a1650` | 1 | swap_elements:30 | 566 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 3 | `d15956b37d36` | 1 | swap_elements_opt3:26 | 566 |
|  | 3 | `cb6115298290` | 1 | hex_stdio:40 | 542 |
|  | 3 | `f3055b207088` | 1 | hex_stdio:6 | 477 |
|  | 3 | `d3791d2e231a` | 1 | hex_stdio:72 | 441 |
|  | 3 | `58ea9f467549` | 1 | hex_stdio:1 | 436 |
|  | 3 | `bccced5afae2` | 1 | hex_stdio:9 | 426 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 0 | `9bac5d2d1f41` | 1 | float_minmax:33 | 402 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 0 | `8dbfa419f0d0` | 1 | float_trunc:27 | 402 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 0 | `0b90bb6ff105` | 1 | rust_u64:38 | 402 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 0 | `70ef752cb0fc` | 1 | rust_u64_tests:46 | 402 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 0 | `57e454fe76ef` | 1 | swap_elements:29 | 402 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 3 | `3b813a27757c` | 1 | swap_elements_opt3:25 | 402 |
|  | 3 | `25cd153d08c0` | 1 | hex_stdio:0 | 387 |
| <u64 as num_integer::Integer>::gcd | 0 | `2eaf6cced17b` | 1 | num_integer:1 | 376 |
|  | 3 | `371b48f60017` | 1 | hex_stdio:8 | 360 |
|  | 3 | `7c2a6efb167d` | 1 | hex_stdio:68 | 347 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 0 | `77c4bdc6ef01` | 1 | float_minmax:38 | 334 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 0 | `17d65cf48bf2` | 1 | float_trunc:32 | 334 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 0 | `c66afc6336e1` | 1 | rust_u64:43 | 334 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 0 | `fba870152995` | 1 | rust_u64_tests:51 | 334 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 0 | `ae7a94082128` | 1 | swap_elements:34 | 334 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 3 | `5c61b8796a14` | 1 | swap_elements_opt3:30 | 334 |
|  | 3 | `af515839c5d3` | 1 | hex_stdio:63 | 333 |
| _RNvCsfLfy6EI15iL_7___rustc26___rust_alloc_error_handler | 3 | `6ab50f420ff6` | 1 | mergesort:46 | 333 |
|  | 3 | `dd7007bf9cf0` | 1 | hex_stdio:74 | 330 |
|  | 3 | `7517378cd2ca` | 1 | hex_stdio:94 | 330 |
| _RNvXs8_NtNtNtCsgXGp5Oqx2Ny_4core3fmt3num3impmNtB9_7Display… | 0 | `8f31fba5e8b1` | 1 | float_minmax:65 | 319 |
|  | 3 | `af71546043bb` | 1 | hex_stdio:84 | 319 |
| _RNvXNtNtCsebHcaeoSrxy_3std2io5errorNtB2_5ErrorNtNtCsgXGp5O… | 3 | `c2c56fda1751` | 1 | mergesort:54 | 319 |
| _RNvXs8_NtNtNtCsgXGp5Oqx2Ny_4core3fmt3num3impmNtB9_7Display… | 0 | `f945d3470a97` | 1 | swap_elements:61 | 319 |
| _RNvXs8_NtNtNtCsgXGp5Oqx2Ny_4core3fmt3num3impmNtB9_7Display… | 3 | `68c7cf060052` | 1 | swap_elements_opt3:57 | 319 |
| _RNvNtCsebHcaeoSrxy_3std9panicking15panic_with_hook | 0 | `ea7623d2b310` | 1 | float_minmax:23 | 274 |
| _RNvNtCsebHcaeoSrxy_3std9panicking15panic_with_hook | 0 | `d79b261d7290` | 1 | float_trunc:17 | 274 |
|  | 3 | `07b47f41eab6` | 1 | hex_stdio:29 | 274 |
| _RNvCsfLfy6EI15iL_7___rustc18___rust_start_panic | 3 | `02c2f96e7b2e` | 1 | mergesort:22 | 274 |
| _RNvNtCsebHcaeoSrxy_3std9panicking15panic_with_hook | 0 | `78a831bd3b0b` | 1 | rust_u64:28 | 274 |
| _RNvNtCsebHcaeoSrxy_3std9panicking15panic_with_hook | 0 | `787d99de6c59` | 1 | rust_u64_tests:36 | 274 |
| _RNvNtCsebHcaeoSrxy_3std9panicking15panic_with_hook | 0 | `8efb4e8e1e23` | 1 | swap_elements:19 | 274 |
| _RNvNtCsebHcaeoSrxy_3std9panicking15panic_with_hook | 3 | `06898ac3b653` | 1 | swap_elements_opt3:15 | 274 |
| _RNvXs_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB4_… | 0 | `8260512a9d5b` | 1 | float_minmax:50 | 265 |
| _RNvXs_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB4_… | 0 | `91bf8d8e8649` | 1 | float_trunc:44 | 265 |
|  | 3 | `8158d4f34684` | 1 | hex_stdio:52 | 265 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 3 | `5e78ac5409e4` | 1 | mergesort:40 | 265 |
| _RNvXs_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB4_… | 0 | `d56965890597` | 1 | rust_u64:55 | 265 |
| _RNvXs_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB4_… | 0 | `29960126b568` | 1 | rust_u64_tests:63 | 265 |
| _RNvXs_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB4_… | 0 | `3eae5dbcc3b6` | 1 | swap_elements:46 | 265 |
| _RNvXs_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB4_… | 3 | `30ef2688bfb4` | 1 | swap_elements_opt3:42 | 265 |
| float_minmax::exports::naive_max | 0 | `e16be06d8d6a` | 1 | float_minmax:4 | 259 |
| float_minmax::exports::naive_min | 0 | `7bb7c79be3fe` | 1 | float_minmax:5 | 259 |
|  | 3 | `c57482568b57` | 1 | hex_stdio:81 | 246 |
| float_minmax::exports::opt_max | 0 | `c962799bc6cd` | 1 | float_minmax:0 | 204 |
| float_minmax::exports::opt_min | 0 | `b01258f3b673` | 1 | float_minmax:2 | 204 |
|  | 3 | `ff60beb054c2` | 1 | hex_stdio:88 | 200 |
|  | 3 | `5d9c741c4361` | 1 | hex_stdio:75 | 177 |
|  | 3 | `0161b12ef8f9` | 1 | xor:0 | 177 |
| _RNvXs_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB4_… | 0 | `58e4578b6652` | 1 | float_minmax:49 | 165 |
| _RNvXs_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB4_… | 0 | `0205e564be9b` | 1 | float_trunc:43 | 165 |
|  | 3 | `53679ee1249c` | 1 | hex_stdio:51 | 165 |
| _RNvCsfLfy6EI15iL_7___rustc13___rdl_dealloc | 3 | `b0dfc52187c9` | 1 | mergesort:39 | 165 |
| _RNvXs_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB4_… | 0 | `a55bd8c41f5d` | 1 | rust_u64:54 | 165 |
| _RNvXs_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB4_… | 0 | `85e49563e196` | 1 | rust_u64_tests:62 | 165 |
| _RNvXs_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB4_… | 0 | `1467da3874b0` | 1 | swap_elements:45 | 165 |
| _RNvXs_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB4_… | 3 | `f62abb157d25` | 1 | swap_elements_opt3:41 | 165 |
|  | 3 | `8ad6209fe1e9` | 1 | hex_stdio:2 | 159 |
|  | 3 | `0d0ca312b0aa` | 1 | hex_stdio:15 | 157 |
| core::ptr::drop_in_place<std::io::default_write_fmt::Adapte… | 3 | `e3f6a70af436` | 1 | mergesort:8 | 157 |
| _RNCNvNtCsebHcaeoSrxy_3std9panicking13panic_handler0B5_ | 0 | `b98f49df6e30` | 1 | float_minmax:21 | 154 |
| _RNCNvNtCsebHcaeoSrxy_3std9panicking13panic_handler0B5_ | 0 | `45bfdcdb68e8` | 1 | float_trunc:15 | 154 |
|  | 3 | `61461eba32e7` | 1 | hex_stdio:27 | 154 |
| <talos_stdio::ExtIO as std::io::Read>::read | 3 | `fcb9779fa73e` | 1 | mergesort:20 | 154 |
| _RNCNvNtCsebHcaeoSrxy_3std9panicking13panic_handler0B5_ | 0 | `ca390651ca9c` | 1 | rust_u64:26 | 154 |
| _RNCNvNtCsebHcaeoSrxy_3std9panicking13panic_handler0B5_ | 0 | `6cbb9ca595e2` | 1 | rust_u64_tests:34 | 154 |
| _RNCNvNtCsebHcaeoSrxy_3std9panicking13panic_handler0B5_ | 0 | `12955f245c26` | 1 | swap_elements:17 | 154 |
| _RNCNvNtCsebHcaeoSrxy_3std9panicking13panic_handler0B5_ | 3 | `3804b1ccbeca` | 1 | swap_elements_opt3:13 | 154 |
|  | 3 | `b809161d1baa` | 1 | gcd_stdio:0 | 149 |
| core::ptr::drop_in_place<std::io::error::Error> | 3 | `68d09dc47a4d` | 1 | mergesort:9 | 146 |
|  | 3 | `57ff8e635731` | 1 | hex_stdio:58 | 144 |
| float_round::exports::naive_round | 0 | `cb536f73008a` | 1 | float_round:0 | 140 |
|  | 3 | `dad385c4a522` | 1 | hex_stdio:73 | 139 |
|  | 3 | `0ec685bc12e2` | 1 | hex_stdio:10 | 134 |
| entrypoint | 0 | `febd0673ecb3` | 1 | rust_u64:7 | 133 |
|  | 3 | `0bf8db4d092a` | 1 | hex_stdio:96 | 126 |
|  | 3 | `59108f80d303` | 1 | hex_stdio:97 | 126 |
| check_max | 0 | `270f0b47fa8f` | 1 | float_minmax:7 | 124 |
| check_min | 0 | `b173777df796` | 1 | float_minmax:8 | 124 |
|  | 3 | `168162aaccb7` | 1 | hex_stdio:4 | 124 |
| float_trunc::exports::naive_trunc | 0 | `fbc3dbe7d2dc` | 1 | float_trunc:0 | 123 |
|  | 3 | `0d68670bd207` | 1 | hex_stdio:12 | 123 |
|  | 3 | `55a1c0c33a11` | 1 | hex_stdio:59 | 123 |
| core::fmt::Write::write_char | 3 | `22523b0c3d01` | 1 | mergesort:5 | 123 |
| _RNvCsfLfy6EI15iL_7___rustc13___rdl_dealloc | 0 | `0425d23f8568` | 1 | float_minmax:30 | 112 |
| check_abs | 0 | `e971903e5091` | 1 | float_reinterpret:10 | 112 |
| _RNvCsfLfy6EI15iL_7___rustc13___rdl_dealloc | 0 | `1f8181e324eb` | 1 | float_trunc:24 | 112 |
|  | 3 | `81c48ad4ac85` | 1 | gcd_stdio:6 | 112 |
| entrypoint | 0 | `fdfbcd373775` | 1 | rust_array:3 | 112 |
| _RNvCsfLfy6EI15iL_7___rustc13___rdl_dealloc | 0 | `39cf6bd70472` | 1 | rust_u64:35 | 112 |
| _RNvCsfLfy6EI15iL_7___rustc13___rdl_dealloc | 0 | `32c275adb113` | 1 | rust_u64_tests:43 | 112 |
| _RNvCsfLfy6EI15iL_7___rustc13___rdl_dealloc | 0 | `bba81697f977` | 1 | swap_elements:26 | 112 |
| _RNvCsfLfy6EI15iL_7___rustc13___rdl_dealloc | 3 | `636e80694b92` | 1 | swap_elements_opt3:22 | 112 |
|  | 3 | `64454f010296` | 1 | hex_stdio:90 | 110 |
|  | 3 | `88cded55743d` | 1 | hex_stdio:18 | 107 |
|  | 3 | `0111dd27641c` | 1 | hex_stdio:3 | 105 |
| swap_elements | 3 | `52a1b9c4a58b` | 1 | swap_elements_opt3:0 | 99 |
|  | 3 | `44ef9b06db41` | 1 | hex_stdio:93 | 96 |
| _RNvNtCsgXGp5Oqx2Ny_4core9panicking18panic_bounds_check | 0 | `5e352bafc13a` | 1 | float_minmax:60 | 95 |
|  | 3 | `32e67ddc833f` | 1 | hex_stdio:70 | 95 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 3 | `52868e7ca69e` | 1 | mergesort:49 | 95 |
| _RNvXs6_NtNtCsebHcaeoSrxy_3std2io5errorNtNtB5_13repr_unpack… | 3 | `8042f7b448c0` | 1 | mergesort:55 | 95 |
| _RNvNtCsgXGp5Oqx2Ny_4core9panicking18panic_bounds_check | 0 | `41fddf5069d1` | 1 | swap_elements:56 | 95 |
| _RNvNtCsgXGp5Oqx2Ny_4core9panicking18panic_bounds_check | 3 | `0efc379fd91a` | 1 | swap_elements_opt3:52 | 95 |
| _RNvNtNtCsebHcaeoSrxy_3std9panicking11panic_count8increase | 0 | `7d572cc5328e` | 1 | float_minmax:39 | 94 |
| _RNvNtNtCsebHcaeoSrxy_3std9panicking11panic_count8increase | 0 | `a87507a4b3ec` | 1 | float_trunc:33 | 94 |
|  | 3 | `3643e61adbda` | 1 | hex_stdio:36 | 94 |
| _RINvNtNtCsebHcaeoSrxy_3std3sys9backtrace26___rust_end_shor… | 3 | `248d4ffeba45` | 1 | mergesort:29 | 94 |
| _RNvNtNtCsebHcaeoSrxy_3std9panicking11panic_count8increase | 0 | `7123f3e7ca83` | 1 | rust_u64:44 | 94 |
| _RNvNtNtCsebHcaeoSrxy_3std9panicking11panic_count8increase | 0 | `d7313ddd72ad` | 1 | rust_u64_tests:52 | 94 |
| _RNvNtNtCsebHcaeoSrxy_3std9panicking11panic_count8increase | 0 | `3e33eeeae971` | 1 | swap_elements:35 | 94 |
| _RNvNtNtCsebHcaeoSrxy_3std9panicking11panic_count8increase | 3 | `b4ad1026e02b` | 1 | swap_elements_opt3:31 | 94 |
| check_copysign | 0 | `a16820891107` | 1 | float_reinterpret:11 | 92 |
| core::slice::_<impl [T]>::swap | 0 | `5e4738a151ba` | 1 | swap_elements:1 | 89 |
| check_round | 0 | `25900cd0f849` | 1 | float_round:6 | 88 |
|  | 3 | `86f8beff82d1` | 1 | byte_echo:0 | 87 |
| _RNvXs1_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB5… | 0 | `ca6007e8fad2` | 1 | float_minmax:45 | 84 |
| _RNvXs1_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB5… | 0 | `b40a492c14fb` | 1 | float_trunc:39 | 84 |
|  | 3 | `af3a4e1cd521` | 1 | hex_stdio:44 | 84 |
| _RNvCsfLfy6EI15iL_7___rustc11___rdl_alloc | 3 | `712fb59ba952` | 1 | mergesort:35 | 84 |
| _RNvXs1_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB5… | 0 | `b2df765dcf73` | 1 | rust_u64:50 | 84 |
| _RNvXs1_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB5… | 0 | `34339044adc1` | 1 | rust_u64_tests:58 | 84 |
| swap_elements | 0 | `f008afad1008` | 1 | swap_elements:4 | 84 |
| _RNvXs1_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB5… | 0 | `61ba372f8952` | 1 | swap_elements:41 | 84 |
| _RNvXs1_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB5… | 3 | `a86e01589b0c` | 1 | swap_elements_opt3:37 | 84 |
|  | 3 | `5d6369d3d8d1` | 1 | hex_stdio:80 | 73 |
| num_integer::gcd_u64 | 0 | `04a031f92e96` | 1 | num_integer:0 | 68 |
|  | 3 | `aa4429d7d903` | 1 | hex_stdio:48 | 67 |
| core::f32::_<impl f32>::max | 0 | `ec657cef48e5` | 1 | float_minmax:1, float_minmax:3 | 61 |
|  | 3 | `0bac9d093ace` | 1 | hex_stdio:76 | 57 |
|  | 3 | `d2ad86e16ee1` | 1 | hex_stdio:77 | 53 |
| check | 0 | `7885fd9f3230` | 1 | float_trunc:2 | 49 |
| core::ptr::swap | 0 | `eb887a6bc83a` | 1 | swap_elements:2 | 46 |
| _RNCNvNtCsebHcaeoSrxy_3std5alloc8rust_oom0B5_ | 0 | `a166ca8685bb` | 1 | float_minmax:19 | 44 |
| _RNCNvNtCsebHcaeoSrxy_3std5alloc8rust_oom0B5_ | 0 | `214b83600838` | 1 | float_trunc:13 | 44 |
|  | 3 | `48568c33a4ef` | 1 | hex_stdio:25 | 44 |
| _RNvCsfLfy6EI15iL_7___rustc35___rust_no_alloc_shim_is_unsta… | 3 | `02570d1ec232` | 1 | mergesort:18 | 44 |
| _RNCNvNtCsebHcaeoSrxy_3std5alloc8rust_oom0B5_ | 0 | `9439dbfd422c` | 1 | rust_u64:24 | 44 |
| _RNCNvNtCsebHcaeoSrxy_3std5alloc8rust_oom0B5_ | 0 | `ac76856162c6` | 1 | rust_u64_tests:32 | 44 |
| _RNCNvNtCsebHcaeoSrxy_3std5alloc8rust_oom0B5_ | 0 | `5cfb8653d66f` | 1 | swap_elements:15 | 44 |
| _RNCNvNtCsebHcaeoSrxy_3std5alloc8rust_oom0B5_ | 3 | `f9e55b30d65c` | 1 | swap_elements_opt3:11 | 44 |
| float_reinterpret::exports::copysign_bits | 0 | `774e34951525` | 1 | float_reinterpret:4 | 40 |
| div_then_add | 0 | `7625164fea3e` | 1 | rust_u64_tests:4 | 37 |
| div_then_mul | 0 | `ec18be6f5c1a` | 1 | rust_u64_tests:5 | 37 |
| rem_then_add | 0 | `59c67b09616d` | 1 | rust_u64_tests:12 | 37 |
| rem_then_mul | 0 | `c3426bae2b8e` | 1 | rust_u64_tests:13 | 37 |
|  | 3 | `9054d56397ef` | 1 | hex_stdio:45 | 36 |
|  | 3 | `3539187995bf` | 1 | hex_stdio:53 | 36 |
| div | 0 | `664f8285c2b8` | 1 | rust_u64:6 | 34 |
| rem | 0 | `1a6e3be88053` | 1 | rust_u64:10 | 34 |
| core::f32::_<impl f32>::copysign | 0 | `54e6a9348986` | 1 | float_reinterpret:8 | 31 |
| _RNvXNtCsgXGp5Oqx2Ny_4core3anyNtNtCs5cOc02OMXlo_5alloc6stri… | 0 | `0e7944c3555f` | 1 | float_minmax:40 | 30 |
| _RNvXNtCsgXGp5Oqx2Ny_4core3anyReNtB2_3Any7type_idCsebHcaeoS… | 0 | `6f6d64264ab3` | 1 | float_minmax:41 | 30 |
| _RNvXNtCsgXGp5Oqx2Ny_4core3anyNtNtCs5cOc02OMXlo_5alloc6stri… | 0 | `77d0b84977a3` | 1 | float_trunc:34 | 30 |
| _RNvXNtCsgXGp5Oqx2Ny_4core3anyReNtB2_3Any7type_idCsebHcaeoS… | 0 | `db9e79f90633` | 1 | float_trunc:35 | 30 |
|  | 3 | `3d6f6943a7d9` | 1 | hex_stdio:37 | 30 |
|  | 3 | `ecffb488ff8b` | 1 | hex_stdio:38 | 30 |
|  | 3 | `d715dab8ad78` | 1 | hex_stdio:83 | 30 |
| _RNCNvNtCsebHcaeoSrxy_3std9panicking13panic_handler0B5_ | 3 | `c257f7d27b5b` | 1 | mergesort:30 | 30 |
| _RNvMs4_NtCs5cOc02OMXlo_5alloc7raw_vecNtB5_11RawVecInner11f… | 3 | `ab7186a0ea65` | 1 | mergesort:31 | 30 |
| _RNvXNtCsgXGp5Oqx2Ny_4core3anyNtNtCs5cOc02OMXlo_5alloc6stri… | 0 | `8261bd3fb639` | 1 | rust_u64:45 | 30 |
| _RNvXNtCsgXGp5Oqx2Ny_4core3anyReNtB2_3Any7type_idCsebHcaeoS… | 0 | `f9016553d95e` | 1 | rust_u64:46 | 30 |
| _RNvXNtCsgXGp5Oqx2Ny_4core3anyNtNtCs5cOc02OMXlo_5alloc6stri… | 0 | `c9fc61472aec` | 1 | rust_u64_tests:53 | 30 |
| _RNvXNtCsgXGp5Oqx2Ny_4core3anyReNtB2_3Any7type_idCsebHcaeoS… | 0 | `745d40f71e95` | 1 | rust_u64_tests:54 | 30 |
| _RNvXNtCsgXGp5Oqx2Ny_4core3anyNtNtCs5cOc02OMXlo_5alloc6stri… | 0 | `caeba10be281` | 1 | swap_elements:36 | 30 |
| _RNvXNtCsgXGp5Oqx2Ny_4core3anyReNtB2_3Any7type_idCsebHcaeoS… | 0 | `3fe4681d4fd6` | 1 | swap_elements:37 | 30 |
| _RNvXNtCsgXGp5Oqx2Ny_4core3anyNtNtCs5cOc02OMXlo_5alloc6stri… | 3 | `e70427d1a9a9` | 1 | swap_elements_opt3:32 | 30 |
| _RNvXNtCsgXGp5Oqx2Ny_4core3anyReNtB2_3Any7type_idCsebHcaeoS… | 3 | `b7343cd3bca2` | 1 | swap_elements_opt3:33 | 30 |
| core::f32::_<impl f32>::abs | 0 | `d4f142906aff` | 1 | float_reinterpret:1 | 29 |
| core::f64::_<impl f64>::abs | 0 | `3c49ed2d8075` | 1 | float_reinterpret:3 | 29 |
| std::f32::_<impl f32>::trunc | 0 | `059e3cf9cc1a` | 1 | float_round:1 | 29 |
| std::f32::_<impl f32>::ceil | 0 | `8dc3fedf449a` | 1 | float_round:2 | 29 |
| std::f32::_<impl f32>::floor | 0 | `5e8ec69b3e0d` | 1 | float_round:3 | 29 |
| std::f32::_<impl f32>::round_ties_even | 0 | `de78fa43b1aa` | 1 | float_round:5 | 29 |
|  | 3 | `e02819aeca84` | 1 | hex_stdio:16 | 28 |
|  | 3 | `76de7f5e4df9` | 1 | hex_stdio:91 | 28 |
|  | 3 | `22d5b0fe8b82` | 1 | hex_stdio:17 | 26 |
| float_reinterpret::exports::abs_bits | 0 | `b9d02081dfd4` | 1 | float_reinterpret:9 | 24 |
| total_variation | 0 | `572fbabd75fc` | 1 | total_variation:1 | 24 |
| _RNvNtCs5cOc02OMXlo_5alloc7raw_vec17capacity_overflow | 0 | `d5270ae50e9e` | 1 | float_minmax:56 | 23 |
| _RNvNtCs5cOc02OMXlo_5alloc7raw_vec17capacity_overflow | 0 | `cd04e767c1c3` | 1 | float_trunc:50 | 23 |
|  | 3 | `89ab30eea63e` | 1 | hex_stdio:61 | 23 |
| _RNvCsfLfy6EI15iL_7___rustc18___rdl_alloc_zeroed | 3 | `f5dc3757b02f` | 1 | mergesort:45 | 23 |
| _RNvNtCs5cOc02OMXlo_5alloc7raw_vec17capacity_overflow | 0 | `69e3d7326b62` | 1 | rust_u64:61 | 23 |
| _RNvNtCs5cOc02OMXlo_5alloc7raw_vec17capacity_overflow | 0 | `525a0946ab12` | 1 | rust_u64_tests:69 | 23 |
| swap_elements::swap_elements | 0 | `0398cb6c4911` | 1 | swap_elements:0 | 23 |
| _RNvNtCs5cOc02OMXlo_5alloc7raw_vec17capacity_overflow | 0 | `fd03a257badd` | 1 | swap_elements:52 | 23 |
| _RNvNtCs5cOc02OMXlo_5alloc7raw_vec17capacity_overflow | 3 | `112d0507441e` | 1 | swap_elements_opt3:48 | 23 |
| is_empty | 0 | `8ea3298e5df1` | 1 | rust_array:5 | 22 |
| empty_xor_flag | 0 | `3fee3f314d75` | 1 | rust_array_tests:6, rust_array_tests:7 | 21 |
| _RNvXs1_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB5… | 0 | `93c17967b431` | 1 | float_minmax:43 | 20 |
| _RNvYNtNtCs5cOc02OMXlo_5alloc6string6StringNtNtCsgXGp5Oqx2N… | 0 | `09a48e9695e6` | 1 | float_minmax:52 | 20 |
| fmaxf | 0 | `36eb1a7f777b` | 1 | float_minmax:66 | 20 |
| fminf | 0 | `9c863f614134` | 1 | float_minmax:67 | 20 |
| _RNvXs1_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB5… | 0 | `2d10b3a5107e` | 1 | float_trunc:37 | 20 |
| _RNvYNtNtCs5cOc02OMXlo_5alloc6string6StringNtNtCsgXGp5Oqx2N… | 0 | `76b7c6469f19` | 1 | float_trunc:46 | 20 |
|  | 3 | `f259e3df3a06` | 1 | hex_stdio:42 | 20 |
|  | 3 | `16b2fac5c0ad` | 1 | hex_stdio:46 | 20 |
|  | 3 | `cb80f797b4de` | 1 | hex_stdio:54 | 20 |
|  | 3 | `80dbc2d7850c` | 1 | hex_stdio:56 | 20 |
|  | 3 | `0cd4d7a8734d` | 1 | hex_stdio:98 | 20 |
| _RNvNtCsebHcaeoSrxy_3std5alloc24default_alloc_error_hook | 3 | `f97a490cd456` | 1 | mergesort:33 | 20 |
| _RNvMs0_NtCsjqx8TIyZbP9_8dlmalloc8dlmallocINtB5_8DlmallocNt… | 3 | `e03815ccabcf` | 1 | mergesort:42 | 20 |
| _RNvXs1_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB5… | 0 | `17a104771811` | 1 | rust_u64:48 | 20 |
| _RNvYNtNtCs5cOc02OMXlo_5alloc6string6StringNtNtCsgXGp5Oqx2N… | 0 | `a44e578f4cfc` | 1 | rust_u64:57 | 20 |
| _RNvNtNtCsgXGp5Oqx2Ny_4core9panicking11panic_const23panic_c… | 0 | `0088a4682108` | 1 | rust_u64:67 | 20 |
| _RNvXs1_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB5… | 0 | `dc477aa6261e` | 1 | rust_u64_tests:56 | 20 |
| _RNvYNtNtCs5cOc02OMXlo_5alloc6string6StringNtNtCsgXGp5Oqx2N… | 0 | `d1f47059b703` | 1 | rust_u64_tests:65 | 20 |
| _RNvNtNtCsgXGp5Oqx2Ny_4core9panicking11panic_const23panic_c… | 0 | `2d9e1bed782c` | 1 | rust_u64_tests:75 | 20 |
| _RNvXs1_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB5… | 0 | `c940305c80a7` | 1 | swap_elements:39 | 20 |
| _RNvYNtNtCs5cOc02OMXlo_5alloc6string6StringNtNtCsgXGp5Oqx2N… | 0 | `52325fc09bbc` | 1 | swap_elements:48 | 20 |
| _RNvXs1_NvNtCsebHcaeoSrxy_3std9panicking13panic_handlerNtB5… | 3 | `4f4d872a828c` | 1 | swap_elements_opt3:35 | 20 |
| _RNvYNtNtCs5cOc02OMXlo_5alloc6string6StringNtNtCsgXGp5Oqx2N… | 3 | `fbf07f6ebbf5` | 1 | swap_elements_opt3:44 | 20 |
|  | 3 | `0aa4d34c2eba` | 1 | hex_stdio:85 | 19 |
|  | 3 | `1d7e96d80232` | 1 | hex_stdio:89 | 19 |
|  | 3 | `745041a0a9f4` | 1 | hex_stdio:92 | 19 |
| rust_array_tests::empty_xor_flag | 0 | `81f87984500f` | 1 | rust_array_tests:2 | 19 |
| rust_array_tests::empty_plus_three | 0 | `af1df912b5eb` | 1 | rust_array_tests:4 | 19 |
| _RNvNtNtCsgXGp5Oqx2Ny_4core9panicking11panic_const23panic_c… | 0 | `0da7000c9a70` | 1 | rust_u64:66 | 19 |
| shl_twice | 0 | `55593bd296bf` | 1 | rust_u64_tests:15 | 19 |
| shr_twice | 0 | `78d6d18edd45` | 1 | rust_u64_tests:17 | 19 |
| _RNvNtNtCsgXGp5Oqx2Ny_4core9panicking11panic_const23panic_c… | 0 | `5a99198dfb3b` | 1 | rust_u64_tests:74 | 19 |
| rust_array::is_empty | 0 | `3d89e9e093c3` | 1 | rust_array:1 | 16 |
| shl_then_add | 0 | `a8e04f621f6f` | 1 | rust_u64_tests:14 | 15 |
| shr_then_sub | 0 | `891cdb221fc1` | 1 | rust_u64_tests:16 | 15 |
| _RNvNtCsebHcaeoSrxy_3std5alloc24default_alloc_error_hook | 0 | `b8cfc90d60ef` | 1 | float_minmax:24 | 13 |
| float_reinterpret::exports::abs_promote | 0 | `b22e66d85047` | 1 | float_reinterpret:2 | 13 |
| float_reinterpret::exports::copysign_native | 0 | `e64ca389c51a` | 1 | float_reinterpret:7 | 13 |
| _RNvNtCsebHcaeoSrxy_3std5alloc24default_alloc_error_hook | 0 | `63570e2a2191` | 1 | float_trunc:18 | 13 |
|  | 3 | `e1fc1e8d4ed2` | 1 | hex_stdio:30 | 13 |
| _RINvNvMs2_NtCs5cOc02OMXlo_5alloc7raw_vecINtB8_11RawVecInne… | 3 | `5b88c5619f5c` | 1 | mergesort:23 | 13 |
| _RNvNtCsebHcaeoSrxy_3std5alloc24default_alloc_error_hook | 0 | `5a83f7bb4f88` | 1 | rust_u64:29 | 13 |
| _RNvNtCsebHcaeoSrxy_3std5alloc24default_alloc_error_hook | 0 | `8aa7093a14bd` | 1 | rust_u64_tests:37 | 13 |
| _RNvNtCsebHcaeoSrxy_3std5alloc24default_alloc_error_hook | 0 | `485986d651df` | 1 | swap_elements:20 | 13 |
| _RNvNtCsebHcaeoSrxy_3std5alloc24default_alloc_error_hook | 3 | `e9454736a71e` | 1 | swap_elements_opt3:16 | 13 |
|  | 3 | `7a37486e4d22` | 1 | hex_stdio:39 | 12 |
| shl | 0 | `757e9a6c77e2` | 1 | rust_u64:12 | 12 |
| shr | 0 | `b710b10c2c3c` | 1 | rust_u64:13 | 12 |
| add_chain | 0 | `34efb0b67824` | 1 | rust_u64_tests:0 | 11 |
| add_then_mul | 0 | `1f692edfb4c9` | 1 | rust_u64_tests:1 | 11 |
| and_chain | 0 | `1069c79eb0ae` | 1 | rust_u64_tests:2 | 11 |
| and_then_or | 0 | `61c9140ddf05` | 1 | rust_u64_tests:3 | 11 |
| mul_chain | 0 | `cdbd4701b679` | 1 | rust_u64_tests:6 | 11 |
| mul_then_add | 0 | `60c3e0984137` | 1 | rust_u64_tests:7 | 11 |
| not_then_xor | 0 | `e60ba994dc5e` | 1 | rust_u64_tests:8 | 11 |
| not_twice | 0 | `5ec1042ec114` | 1 | rust_u64_tests:9 | 11 |
| or_chain | 0 | `95e6dde9ca3d` | 1 | rust_u64_tests:10 | 11 |
| or_then_xor | 0 | `1e033f122baf` | 1 | rust_u64_tests:11 | 11 |
| sub_chain | 0 | `9b15d6715523` | 1 | rust_u64_tests:18 | 11 |
| sub_then_add | 0 | `a549ca63fe90` | 1 | rust_u64_tests:19 | 11 |
| xor_chain | 0 | `d29eebb36155` | 1 | rust_u64_tests:20 | 11 |
| xor_then_and | 0 | `dc66de200031` | 1 | rust_u64_tests:21 | 11 |
| rust_array_tests::len_plus_arg | 0 | `c54c1ad08158` | 1 | rust_array_tests:0 | 8 |
| rust_array_tests::len_plus_one | 0 | `bf017135016c` | 1 | rust_array_tests:1 | 8 |
| add | 0 | `a30ee6b183e2` | 1 | rust_u64:2 | 8 |
| bitand | 0 | `586f44f55b8d` | 1 | rust_u64:3 | 8 |
| bitor | 0 | `453da37d0cf4` | 1 | rust_u64:4 | 8 |
| bitxor | 0 | `18c47bfe1ea5` | 1 | rust_u64:5 | 8 |
| sub | 0 | `61367cb38df6` | 1 | rust_u64:8 | 8 |
| mul | 0 | `c6bdc6138769` | 1 | rust_u64:9 | 8 |
| not | 0 | `c0d02c7d8e47` | 1 | rust_u64:11 | 8 |
| float_trunc::exports::sat_trunc | 0 | `50190f699cc1` | 1 | float_trunc:1 | 7 |
| core::f32::_<impl f32>::to_bits | 0 | `3a041bb139ff` | 1 | float_reinterpret:5 | 6 |
| core::f32::_<impl f32>::from_bits | 0 | `8259f222b174` | 1 | float_reinterpret:6 | 6 |
| rust_array::len | 0 | `567d5b86c22b` | 1 | rust_array:0 | 5 |
