# SAW

[English](saw.md) | 日本語

crate の実装層が NSA の Cryptol と等しいことを、固定サイズで、2 つの経路で証明する SAW の証明。
経路は、crate の rustc の LLVM bitcode の上（`llvm_verify`。SPARK の crate の経路）と、MIR の上（`mir_verify`。NSA 自身の Rust の証明 `algorithms/AES/rust/*/theorems/saw.py` の経路）である。
SPARK の crate の `spark/doc/saw.md`（github.com/manthonyaiello/Foundation、タグ `spark-v1.0`）に対応する文書である。
証明は CI ではなく手元で回し、最後の実行の記録は `saw/results.txt` にある。
[README](../README.ja.md) へ戻る。

## SAW が証明すること

SAW は**実装**層が NSA の Cryptol と等しいことを、Verus の spec 層とも Verus とも独立に、直接証明する。
対象は、`aes::aes_impl` の末端、ラウンド、各鍵長での鍵スケジュールと暗号、`aes::aes_impl::main` の `encrypt` と `decrypt` で、`algorithms/AES/{GF28,SBox,Cipher,KeyExpansion,Main}.cry` に対して証明する。
また SHA-256 の末端と圧縮関数を全入力で、一括の SHA-256 と HMAC-SHA-256 を固定の長さで、`algorithms/SHA2/Main.cry` と `algorithms/HMAC/Main.cry` に対して証明する。
NSA の Cryptol は手を加えずに import する。
**2 つの経路は、同じ関数を、同じ Cryptol に対して、同じ override と tactic で証明する。** スクリプトも 1 つずつ対応する（`saw/llvm/` と `saw/mir/`）。
違うのは SAW が読むもの（bitcode か MIR か）だけで、そのため契約での引数の書き方が違う。

**SAW はサイズごとに別々に証明し、Verus はすべてのサイズを扱う。**
`compress` はすべてのハッシュ値とブロックについて証明するが、`hash` と `hmac_sha256` はスライスを受け取り、SAW はそれを一度に 1 つの長さで実行する。下の表の 1 行が 1 つの長さである。
Verus は同じ関数をすべての長さ（`2^61` バイト未満）について Verus の spec 層に対して証明し、その spec 層を FFI での突き合わせが同じ Cryptol に対してテストする。

### AES

| Rust（`aes::aes_impl::`） | Cryptol | サイズ | override | tactic |
|---|---|---|---|---|
| `x_times` | `GF28.cry`: `xTimes` | | | rme |
| `dot` | `GF28.cry`: `(•)` | | | rme |
| `sub_byte`、`inv_sub_byte` | `SBox.cry`: `\b -> SBox @ b`、`\b -> InvSBox @ b` | | | rme |
| `sub_bytes`、`inv_sub_bytes` | `Cipher.cry`: `SubBytes`、`InvSubBytes` | | `sub_byte`、`inv_sub_byte` | rme |
| `shift_rows`、`inv_shift_rows` | `ShiftRows`、`InvShiftRows` | | | rme |
| `add_round_key` | `AddRoundKey` | | | rme |
| `mix_column` | `MixColumnsStep` | | `x_times` | rme |
| `inv_mix_byte` | `\a b c d -> InvMixColumnsStep [a, b, c, d] @ 0` | | `x_times` | rme |
| `inv_mix_column` | `InvMixColumnsStep` | | `inv_mix_byte` | rme |
| `column`（private） | `\s j -> (split s : [4]AESWord) @ j`、`j < 4` | | | z3（rme は 64 ビットの `4 * j` で終わらなかった） |
| `mix_columns`、`inv_mix_columns` | `MixColumns`、`InvMixColumns` | | `column`、列のステップ | rme |
| `round`、`inv_round` | `Round`、`InvRound` | | その 4 つのステップ | rme |
| `inv_round_prime` | `InvRound'` | | その 4 つのステップ | z3、4 つを uninterpreted（rme: 14 分で終わらず） |
| `sub_word`、`rot_word`、`xor_word` | `KeyExpansion.cry`: `SubWord`、`RotWord`、`^` | | `sub_byte` | rme |
| `rcon` | `(drop`{1} Rcon) @ (i - 1)`、`1 <= i <= 10`（`Rcon @ i`。`Rcon @ 0` は `undefined` で、SAW は記号的な添字でそれを評価してしまう） | | | z3 |
| `expand_key::<k>` | 最初の `Nk k` 個の鍵ワードの ``KeyExpansion`{k}``。15 ブロックの残りは 0 | k = 128、192、256 で鍵ワード `Nk k` 個。k = 128、192 では 8 個でも（`encrypt` が渡す数） | `sub_word`、`rot_word`、`xor_word`、`rcon` | z3、`SubWord` を uninterpreted |
| `encrypt_block::<k>` | 最初の `Nr k + 1` 個のラウンド鍵の ``Cipher`{k}`` | k = 128、192、256 でラウンド鍵 `Nr k + 1` 個。128、192 では 15 個でも | `round`、`sub_bytes`、`shift_rows`、`add_round_key` | z3、`Round`・`SubBytes`・`ShiftRows`・`AddRoundKey` を uninterpreted |
| `decrypt_block::<k>` | ``InvCipher`{k}`` | `encrypt_block` と同じ | `inv_round`、`inv_sub_bytes`、`inv_shift_rows`、`add_round_key` | z3、その 4 つを uninterpreted |
| `decrypt_block_prime::<k>` | ``InvCipher'`{k}`` | k = 128、192、256 | `inv_round_prime` と各ステップ | z3、`InvRound'` と各ステップを uninterpreted |
| `main::encrypt::<k>`、`main::decrypt::<k>` | `Main.cry`: ビットの上の ``AES`{k}.Encrypt``、``.Decrypt`` | k = 128、192、256 | 鍵ワード 8 個の `expand_key`、ラウンド鍵 15 個の `encrypt_block`（`decrypt_block`）（`key_words_of` は実行する） | z3、`KeyExpansion` と `Cipher`（`InvCipher`）を uninterpreted |

「8 個でも」「15 個でも」の長さは、`main::encrypt` と `main::decrypt` が渡すものである（`key_words_of` は `[AESWord; 8]` を、`expand_key` は `[Block; 15]` を返す）。
override は契約が述べるサイズにしか一致しないので、これらの証明があって初めて `encrypt` と `decrypt` がそれを使える。

**SPARK の crate の AES の証明を越えるもの**（SPARK 版が省いたか、できなかったもの）:
`dot`（どの暗号も呼ばない。SPARK の crate のものは SAW で証明していない）、
単独の `sub_word`・`rot_word`・`xor_word`・`rcon`（GNAT-LLVM は SPARK の式関数を `-O0` でも `Expand_Key` に inline 化する。rustc は関数のまま残す）、
`column`、`inv_round_prime` と `decrypt_block_prime`（FIPS 197 の等価な逆暗号。NSA のテンプレートはこれに対して `inv_cipher` を証明している。SPARK の crate は spec 層のものだけを証明する）、
`main::encrypt` と `main::decrypt`（SPARK の crate は spec 層の `Main` を `Main.cry` に対して証明し、`Impl.Main` は FFI で突き合わせる）。

### SHA-256 と HMAC-SHA-256

Cryptol は、SHA-256 のパラメータでの `algorithms/SHA2/Main.cry` の `step` と `hash`、そして `algorithms/HMAC/Main.cry` の `HMAC` である。
これを `saw/SHA256Main.cry` を通して使う。このファイルは、SPARK の crate の `saw/SHA256Main.cry` と同じく、**SHA256.cry 自身のパラメータを写して** `Main` を具体化する。
`SHA256.cry` は `Main` を private に具体化するので、その `step` は名指せない。また SAW 1.6 は `SHA256.cry` をそもそも読み込めない（`packaging/Hash.cry` が import する `algorithms/PBKDF/Main.cry` の翻訳に失敗する）。
`HMAC` は `Hash.cry` と同じく ``HMAC`{λ = 256, B = 64, k, n, L = 32} hash hash hash`` と書く。

| Rust | Cryptol | サイズ（バイト） | override | tactic |
|---|---|---|---|---|
| `sha2::notation::exec::ROTR::<n>`、`SHR::<n>`（12 個の具体化） | `Notation.cry`: ``ROTR`{n, 32}``、``SHR`{n, 32}`` | | | rme |
| `sha2::functions::exec::SIGMA_256_0/1`、`sigma_256_0/1` | `Functions.cry` | | それぞれの 3 つの `ROTR`/`SHR` | rme |
| `sha2::functions::exec::Ch`、`Maj` | `Functions.cry`: `[32]` での `Ch`、`Maj` | | | rme |
| `sha2::sha256_stream::compress` | `Main.cry`: `step` | すべての `h`、`m` | 4 つの sigma、`Ch`、`Maj` | z3、4 つの sigma を uninterpreted |
| `sha2::sha256_stream::hash` | `\msg -> split (hash (join msg))` | 0、1、55、56、63、64、65、100、119、120、128、200 | `compress` | z3、`step` と sigma を uninterpreted（0 では何も） |
| `hmac::sha256_impl::hmac_sha256` | `\key text -> split (HMAC`{256, 64, k, 8 * n, 32} hash hash hash key (join text))` | （鍵、テキスト）: (0, 0)、(32, 3)、(32, 32)、(64, 3)、(64, 32)、(65, 3)、(100, 32) | `compress`。鍵が 65 と 100 では、その長さの `hash` も | z3、`step` と sigma を uninterpreted（(0, 0) では何も） |

長さは SPARK の crate のものである。
パディングの各場合（55: パディングが 1 ブロックに収まる最長のメッセージ。56: 2 ブロック要る最短のもの。64 と 128: ちょうどのブロック。119 と 120: 2 つ目のブロックの中の境目。200: 4 ブロック）と、
`HMAC_init` の各場合（ブロックより短い鍵、ブロックちょうど、長い鍵: 先にハッシュする）を取っている。

- **`compress` は 1 つの関数**で、スケジュールのループと 64 ラウンドのループはその中にある。SPARK の crate と同じである。
  SAW は 64 ラウンドを、すべての呼び出しを override して実行し、z3 は両側で sigma を uninterpreted にする。
  `Ch` と `Maj` は interpreted のままにする。`Functions.cry` のものはタプルを受け取り、SAW 1.6 の what4 のバックエンドはタプルを受け取る uninterpreted な関数を作れないからである。
  feed-forward は core の `u32::wrapping_add`（ループの中の呼び出し）で、実行する
  （SPARK の crate の `Hash_Value` の `"+"` は独立した関数で、z3 で証明している）。
- **記号的な入力がない場合**（0 バイトの `hash`、(0, 0) の `hmac_sha256`）、SAW は override の `step` を定数の上で評価する。そのためそこでは何も uninterpreted にならない。SPARK の crate で分かったのと同じである。
- **lax な算術は使わない。**
  SPARK の crate は、空の範囲を作る証明のために、SHA-256 のモジュールを SAW の lax な算術でもう一度読み込む（GNAT-LLVM の `Lo .. Hi` の長さは、SAW が拒む poison の `add nuw` を作る）。
  Rust の空のスライスはそういう値を作らない。ここではすべての証明が、0 バイトでも、SAW の普通の算術のもとで、コードに rustc のオーバーフロー検査を入れたまま行われる。

### SAW が単独で証明するもの、呼び出し元の中で証明するもの、証明しないもの

下の関数はどれも、Verus が全入力で証明し、FFI で突き合わせている。

| 関数 | どこの中で実行されるか | なぜ単独では証明しないか |
|---|---|---|
| `sha256_stream::init`、`update`、`finalize`、`load_block`、`to_digest` | すべての `hash` の結果（`hash` は `init`、1 回の `update`、`finalize`。override は `compress` だけ） | `update` と `finalize` には、ストリーミングの文脈とその不変条件についての契約が要る。それでも SAW が証明できるのは固定のバッファの埋まり具合とデータの長さでだけである。`load_block` と `to_digest` は呼び出しごとに違うスライスとオフセットを受け取る（SPARK の crate と同じ理由） |
| 同上と、`hmac::sha256_impl::init_key`、`exec::xor_pad`、`init`、`update`、`finalize` | すべての `hmac_sha256` の結果 | 逐次のインターフェースは、一括の `hmac_sha256` と同じ関数である |
| `sha256_stream::hash_chunked`、`ffi::hmac_sha256::hmac_chunked` | なし | 主張は、メッセージをチャンクに分けるすべての分け方についての digest である。SAW が確かめられるのは特定の分け方だけである |
| `aes::aes_impl::main::key_words_of` | `main::encrypt`、`main::decrypt` | バイトの組み直しで、Cryptol に独自の名前がない（`AES`{k}.Encrypt` の中の `split (split key)`） |

### spec 層

SPARK の crate は、ghost コードを有効にしてビルドした bitcode（`-gnatec=saw/spec.adc`）の上で、ghost の spec 層も Cryptol と等しいと証明している。
Verus の spec 関数はまったくコンパイルされない。`cargo build` も `rustc --emit=llvm-bc` も mir-json も、`verus!` の spec と proof のコードを消去した crate を見る。そのため SAW が読む spec 層の bitcode も MIR もない（spec 層の FFI エクスポートがないのと同じである: [ffi.ja.md](ffi.ja.md)）。
spec 層は代わりに実装を通して Cryptol に結びつく。Verus が各実装関数をその spec 関数と等しいと証明し、SAW（これらのサイズで）と FFI での突き合わせ（ランダムと全数の入力で）が実装を Cryptol と等しいと示す。

## なぜ固定サイズか

SPARK の crate（その `doc/saw.md` の "Why fixed sizes: what NSA's own proofs do"）と同じである。
このリポジトリにある NSA の実装の証明 `algorithms/AES/rust/Cipher/theorems/saw.py` と `KeyExpansion/theorems/saw.py` は、暗号・逆暗号・鍵拡張を k = 128・192・256 で、鍵長ごとに 1 つの証明で証明する。ここでの証明も同じ 3 つのサイズである。
SHA-256 と HMAC には NSA の実装の証明がない。その長さは SAW 自身から来る。SAW はコードを記号的に実行するので、ループの上限とバッファのサイズは具体的でなければならない。
Verus が加えるのは、すべてのサイズ、すべてのチャンク分け、すべての呼び出しの順序（`hash_chunked` とストリーミングのインターフェース）と、すべての入力での実行時エラーの不在である。
SAW が加えるのは、rustc が実際にコンパイルするコードを、Verus の spec 層を挟まずに NSA 自身の Cryptol と突き合わせることである。

## bitcode

`check-saw.sh` は `rust-toolchain.toml` のツールチェーン（rustc 1.98.1、LLVM 22）でライブラリをコンパイルする:

```console
$ cargo rustc --lib -- --emit=llvm-bc,llvm-ir,dep-info -C codegen-units=1 -C debuginfo=0 -C no-prepopulate-passes
```

- **dev プロファイル**（`-O0`、オーバーフローの検査、debug assertion）: 検査の panic は呼び出しで、証明するサイズではそれが到達不能だと SAW が見つけなければならない。
- **`codegen-units=1`**: LLVM のモジュールが 1 つになるので、どの override も検証するモジュールのものになる（SAW はそのモジュールからしか override を取らない）。
  generic な関数の k = 128・192・256 の具体化がそこに入るのは、crate の `ffi` モジュールがそれらを具体化するからである。
- **デバッグ情報なし**。SPARK の crate と同じである（SAW 1.6 は GNAT のものを拒んだ）。
- **`-C no-prepopulate-passes`**: LLVM のパスを 1 つも回さない。
  `-O0` でも rustc は LLVM の always-inliner を回し、`#[inline(always)]` の関数（`ROTR`、`SHR`、sigma、`Ch`、`Maj`）を `compress` に inline 化する。
  そうなると、それらの証明は override にできない。z3 は sigma を interpreted にしたままでは、`compress` を `step` に対して 500 秒で証明できなかった。
  このパスがなければそれらは呼び出しのままで、`compress` は sigma を uninterpreted にして 3 秒で証明できる。
  （SPARK の crate が spec 層に `-fno-inline` をつけるのも同じ理由である。）
  変わるのはそれだけで、crate と core の `#[inline(always)]` の関数（`u32::wrapping_add`、スライスの添字、ポインタのキャスト）が inline 化されずに呼び出しになる。
  2026-11-01 に比べたところ、`round`・`mix_columns`・`expand_key::<128>`・`hash` の IR はこのスイッチの有無で 1 行ずつ同じだった。`compress` の IR は、sigma・`Ch`・`Maj` の 6 か所の呼び出しと `u32::wrapping_add` の 11 か所の呼び出しだけが違った。
- **名前。** rustc は名前を mangle する（v0 の方式）。crate のハッシュが入り、それはツールチェーンとビルドで変わる。
  `check-saw.sh` は定義されたシンボルをすべて demangle し（GNU の `c++filt`）、`saw/obj/symbols.saw` を書く。crate の関数（`ffi` モジュールのものは除く）1 つにつき束縛が 1 つである。
  `aes::aes_impl::expand_key::<128>` は `rust__aes__aes_impl__expand_key__128` になる。

rustc が関数をどうするか（x86_64、`.ll` から読んだもの）:

- `u8` は `i8`、`u32` は `i32`、`usize` は `i64`。
- **値渡しの `AESWord`（`[u8; 4]`）は 1 つの `i32`** で、そのバイト `i` はメモリ上の `i` 番目のバイトである。そのためリトルエンディアンのターゲットでは、`i32` はバイトを逆順にして join したものになる。
  契約は新しい `i32` を受け取り、Cryptol には `reverse (split x)` を渡す（override の引数は、SAW が呼び出し元の値と照合できる変数でなければならず、変数の項であってはならない）。
- `&mut Block` や `&[u32; 8]` はポインタ。スライス `&[T]` はデータのポインタと長さの 2 つの引数。
- 値で返す 16 バイトを超える配列（`[Block; 15]`、`[u8; 32]`）は、隠れた第 1 引数のポインタ（`sret`）を通して返す。
  値で渡す `Block`（16 バイト）（`main::encrypt` の `input`）は、呼び出し元の写しへのポインタで渡す。
- Rust の配列の要素 `i` は Cryptol の列の要素 `i` で、`u8` は先頭が最上位ビットの `[8]` である。そのため、ほかには何も並べ替わらない。

## MIR

`check-saw.sh` は mir-json の `cargo saw-build` でライブラリをコンパイルする。
これは crate の MIR を依存先と標準ライブラリの MIR とリンクし、`saw/obj/mir/foundation_verus.linked-mir.json` にする。

- **mir-json 8cbf9af**。SAW 1.6 が submodule として同梱するコミットで、スキーマは 13。SAW 1.6 が読むものである。
  これは rustc のプラグインで、1 つの nightly のツールチェーン **nightly-2026-03-21（rustc 1.96.0-nightly）** 向けにビルドする。crate の 1.98.1 ではない。MIR の経路は、crate をその rustc がコンパイルしたものとして確かめる。
  crate は Verus 自身の検査の外では 1.98 の機能を何も必要とせず（vstd の unstable な機能は Verus が検証するときだけ有効になる）、どちらでもビルドできる。
  `MIR_JSON_DIR` がインストール先（`bin/` と、`mir-json-translate-libs` で翻訳した標準ライブラリの `rlibs/`）を指す。
- `saw-build` は `cargo test` のビルドなので、crate は `cfg(test)` でコンパイルされる。単体テストも MIR に入るが、証明する関数のソースは同じである。
- `-O0` では rustc の MIR の inliner が無効なので、`#[inline(always)]` の関数は bitcode と同じく呼び出しのまま残る（SAW は `compress` の中で sigma の override を 64 回使う）。
- **名前**は Rust のパスである: `foundation_verus::aes::aes_impl::x_times`。
  generic な具体化は名前にハッシュが入り、`mir_find_name crate path [mir_const mir_u32 {{ 128 : [32] }}]` で見つける。
- **型は Rust のもの**: `AESWord` は `mir_array 4 mir_u8`、スライスは割り当ての `mir_slice_value`、`&mut` は `mir_alloc_mut`。
  契約は NSA のテンプレートのものと同じ形である。

## 実行

**`llvm_unsafe_assume_spec` も `mir_unsafe_assume_spec` もない。**
どの override も同じ実行の中での証明であり、`saw/` の下のスクリプトにそれが含まれていれば `check-saw.sh` は実行を拒む。
**`admit`**（や `assume_unsat`、`assume_valid`）もない。これはスクリプトのどこでも、コメントも含め、単語として照合している。

```console
$ PATH=<saw-1.6>/bin:$PATH MIR_JSON_DIR=<mir-json> scripts/check-saw.sh   # 両方の経路。saw/results.txt を書く
$ ... scripts/check-saw.sh --print                                       # 回して記録を表示し、何も書かない
$ SAW_ROUTE=llvm ... scripts/check-saw.sh --print                        # 片方の経路だけ（llvm か mir）
```

`<saw-1.6>` はソルバーつきの SAW 1.6 のリリース、`<mir-json>` は mir-json 8cbf9af のインストール先である（[bootstrap.ja.md](bootstrap.ja.md)）。
片方の経路だけの実行は記録にならない。スクリプトはその場合 `--print` を要求する。

**`saw` の各実行にメモリ上限をかける。** SPARK の crate と同じである。
各実行は独自の systemd の scope で、`MemoryMax=10G`、`MemorySwapMax=0` で動く（`SAW_MEMORY_MAX` で 10G を変えられる）。
上限で kill された実行は失敗であり、上限で kill された陰性対照は失敗したとは数えない。

**陰性対照**は `saw/llvm/negative/*.saw` と `saw/mir/negative/*.saw` で、SPARK の crate の 8 つである。どれも反例つきで失敗しなければならない:

- `x_times` を、簡約なしのシフトに対して: `b = 128`。
- `sub_bytes` を `InvSubBytes` に対して。
- 128 での `expand_key` を、鍵ワードを逆順にした `KeyExpansion` に対して。
- 256 での `encrypt_block` を、ラウンド鍵を逆順にした `Cipher` に対して。
- 128 での `decrypt_block` を、ラウンド鍵を逆順にした `InvCipher` に対して。
- `compress` を、feed-forward で `h` のワードを逆順にして足す `step` に対して（`step h m - h + reverse h`）。
- 56 バイトでの `hash` を、メッセージのバイトを逆順にした `hash` に対して。
- 100 バイトの鍵と 3 バイトのテキストでの `hmac_sha256` を、鍵を逆順にした `HMAC` に対して。

最初の 2 つ以外は、先にその経路のスクリプトを回し、その override と tactic を使う。そのため、override も uninterpreted な関数も証明を空虚にしていないことを示す。

**記録。**
合格した実行はすべて `saw/results.txt` を書く。
内容は、コミット（tree は clean でなければならない）、日付、ホスト、rustc・cargo・c++filt・SAW・z3・mir-json（そのコミットとツールチェーンも）の版、メモリ上限、スイッチ、
bitcode と MIR の sha256、rustc が bitcode のために読んだすべてのソース（その dep-info: crate のもの、vstd のもの、ほかの依存先のもの）の sha256、`Cargo.lock` の sha256、import したすべての NSA の Cryptol ファイルと `saw/SHA256Main.cry` の sha256、
各結果とその tactic と SAW がかけた時間、各陰性対照の反例と時間、経過時間である。
確かめた変更と一緒にコミットする。bitcode と MIR（`saw/obj/`）は追跡しない。

**測定**（`results.txt`。`d59a3f0` での実行、x86_64 の Linux マシン、16 CPU）:
168 件の証明（経路ごとに 84 件: AES 46 件、SHA-256 と HMAC で 38 件）と、失敗すべきとおりに失敗する 16 件の陰性対照で、全部で 928 秒。
証明そのものにかかるのは、11 秒（`llvm/aes_impl.saw`）、30 秒（`llvm/sha256_impl.saw`）、20 秒（`mir/aes_impl.saw`）、159 秒（`mir/sha256_impl.saw`）である。
bitcode の上では、(0, 0) での `hmac_sha256`（11 秒。digest 全体を定数の上で評価する）を除き、どの証明も 3 秒未満である。MIR の上では `hash` と `hmac_sha256` がそれぞれ最大 15 秒かかる。
残りの大半は陰性対照で、これは先にその経路のスクリプトを回す。
