# AES: Verus の spec 層と NSA の Cryptol を並べて

[English](aes.md) | 日本語

crate が 128・192・256 ビットの鍵で AES（FIPS 197）をどう実装し、`algorithms/AES/` の NSA の Cryptol とどう結びつけているか。
SPARK の crate の `spark/doc/walkthroughs/aes.md`（github.com/manthonyaiello/Foundation、タグ `spark-v1.0`）に対応する文書で、節も同じだが短くしてある。
各節は Verus のコードが何をし、どこが違うかを述べる。コードとその doc comment は、節が名指すファイルにある。

層は 2 つあり、その間に lemma がある:

- **spec 層**（`src/aes/`: `types`、`gf28`、`gf2`、`sbox`、`key_expansion`、`cipher`、`main`）。Cryptol のモジュール 1 つにつきモジュール 1 つで、`spec fn` には Cryptol と同じ名前をつける。
  `gf2` は、SBox.cry が import する `shared/algebra/Polynomial/GF2.cry` の部分である。
  Cryptol が自分について述べる性質は `properties` と `sbox_entries` で証明する。
- **実装層**（`aes_impl`、`aes_impl::main`）: バイトの上でその場で動く鍵スケジュール・ラウンドの変換・ブロック暗号。それぞれ、実装する spec 関数を `ensures` する。
  それに鍵とブロックのバイトの上の AES で、ビットの上の Main.cry の `Encrypt` と `Decrypt` と等しいと証明してある。
  lemma は `lemmas` と `main_lemmas` にある。

```text
  NSA の Cryptol（algorithms/AES/*.cry）
        ^                     ^
        | FFI（テスト）       | SAW、k = 128、192、256
        |                     | （bitcode と MIR）
        |                     |
  spec 層（spec fn） ------ properties: Cryptol 自身の性質を証明し直す
        ^                     |
        | Verus、全入力       |
        |                     |
  aes_impl、aes_impl::main（実行可能）
```

SHA-256 と同じく、SPARK の crate にある spec 層から Cryptol への矢印（ghost コードへの FFI での突き合わせと SAW）は、ここにはない。spec 関数はコンパイルされないからである（[ffi.ja.md](../ffi.ja.md)）。
そのため、spec 層自身の振る舞いを証明で確かめるのは、証明し直した性質だけになる（[proving.ja.md](../proving.ja.md#cryptol-自身の性質の証明し直し)）。

## 記法の読み方

[sha-256.ja.md](sha-256.ja.md#記法の読み方) と同じである。
加えて: Cryptol の `{k} (Key k) => ...` は、`const k: u32` について generic で、`recommends Key(k as nat)`（spec）か `requires`（exec）をもつ関数である。
``f`{128}`` は `f::<128>`。`xs @@ is` は prelude の `bulk_index`。`arbitrary()` は何も分かっていない値である。

## spec 層を宣言ごとに

### 型（`Types.cry`）

[`types.rs`](../../src/aes/types.rs)。`Key(k)` は Types.cry の型の制約で、節ごとに写してある。`Nk` と `Nr` は `k as nat` の spec 関数である。
`Block` と `AESWord` は長さ 16 と 4 の `Seq<u8>` で、長さはそれを受け取る関数の `recommends` にする。
ブロックとその 4 つの列の間の `split` と `join` はここにある。SPARK の crate の `Types` と同じである。

**鍵長についての多相**は、2 つの crate がいちばん違うところである。
Ada には型の水準の数がないので、SPARK の crate は `{k}` の関数のために generic な `AES_K` と 3 つの具体化をもち、実行時の鍵長で 1 つを選ぶ ghost の `Spec.Dispatch` をもつ。
ここでは `k` は const generic で、spec のコードでも exec のコードでも値である。そのため `k` について generic な実装 1 つを、同じ `k` の spec に対して一度証明すればよく、3 つのどれも要らない。

### GF(2^8)（`GF28.cry`）

[`gf28.rs`](../../src/aes/gf28.rs)。`dot(b, c)`（Cryptol の `•`）は、`[8] -> [8] -> [15]` と `[15] -> [9] -> [8]` での prelude の `pmod(pmult(b, c), m)` である。`u16` で計算して `u8` にキャストし、キャストで何も失わないことを `lemma_dot` が証明する。
`xTimes(b) = dot(b, 2)`。

### GF(2) の多項式（`shared/algebra/Polynomial/GF2.cry`）

[`gf2.rs`](../../src/aes/gf2.rs)。`pgcd` を通した `inverse` を、SBox.cry が使う型（`a : [8]`、`p : [9]`）で書く。
`pmult` と `pdiv` は prelude のものである（SPARK の crate はどちらもその場に書いている。測った理由がある）。
Cryptol では `pgcd` の局所関数である `inner` を最上位に置き、その再帰は `decreases s[3] when is_state(s) via inner_decreases` とする。
各ステップは `r'` を `r'` を法とする剰余で置き換え、それが小さくなることを `lemma_division` が証明する。

### S-box（`SBox.cry`）

[`sbox.rs`](../../src/aes/sbox.rs)。`SBox` と `InvSBox` は表で、要素ごとに写してある。
`affine(b)` は Cryptol と同じくビット列の上で、prelude の `reverse`・`join`・`value` を通して書く。

### 鍵拡張（`KeyExpansion.cry`）

[`key_expansion.rs`](../../src/aes/key_expansion.rs)。`RotWord`、`SubWord`、`Rcon`（要素 0 は Cryptol では `undefined` で、ここでは `arbitrary()`。SPARK の crate の表には要素 0 がない）。
自分自身を参照する列 `w` は、添字 `i` と、Cryptol が閉じ込めている鍵の再帰関数で、`decreases i when Key(k) && 0 <= i` とする。
`KeyExpansion::<k>` はワードを `Nr k + 1` 個のラウンド鍵に組み直す。
NSA は `KeyExpansion` を `foreign` と宣言し、裏に Rust を置いている。ここで写すのはその Cryptol の本体である。

### ラウンドの変換と暗号（`Cipher.cry`）

[`cipher.rs`](../../src/aes/cipher.rs)。`SubBytes`、`ShiftRows`、`MixColumns`（各列の `MixColumnsStep` を通す）、`AddRoundKey`、それらの逆、`Round`、`InvRound`、`InvRound'`（`InvRound_prime`。Rust の名前に `'` は使えない）、
そして `Cipher`、`InvCipher`、`InvCipher'`。最後の 3 つはどれも、中間のラウンド鍵の上でラウンドを prelude の `foldl` で畳んだもので、`[w0] # ws # [wr]` は `ws[0]`、`ws.subrange(1, Nr)`、`ws[Nr]` とする。
NSA は `Cipher` を `foreign` と宣言している。ここで写すのはその Cryptol の本体である。

### 最上位（`Main.cry`）

[`main.rs`](../../src/aes/main.rs)。Main.cry のレコード ``AES`{k}`` は `struct AES<const k: u32>` で、ビット列の上の関連 spec 関数 `Encrypt` と `Decrypt` をもつ。`AES128` は `type AES128 = AES<128>` である。
ビット・バイト・ワードの間の `split` と `join` は `split_block`、`join_block`、`split_key` である。

### Cryptol 自身の性質（`aes::properties`）

[`properties.rs`](../../src/aes/properties.rs)。SPARK の crate と同じく 15 個のうち 13 個で、どれも性質と同じ名前の `proof fn` とし、その `ensures` が性質の本体である。
鍵長を取る 4 つは、すべての `k` について一度で証明する。
`SBoxCorrect` は [`sbox_entries`](../../src/aes/sbox_entries.rs) で、Verus のインタープリタ（`by (compute_only)`）で表を 1 行ずつ評価する。使うのは `inverse` の関数の trait を使わない写しで、元のものと等しいと証明してある。
`SBoxInverts` も評価で済ませる。
`MixColumnsStepInverts` は、定数との `•` をそれぞれ `xTimes` に書き換え、残りを 1 つの `bit_vector` の問い合わせに任せる。SPARK の crate の線形性の lemma の代わりである。
それぞれがなぜ違うかは、モジュールの doc comment にある。

## Verus での Cryptol の prelude

AES は、`foldl`（ラウンドの fold、GF28MultiplicationCorrect）、`@@`（SubBytes、ShiftRows とその逆）、バイトとビットの間の `join` と `split`、ワードの `@` と `head`、`pmult`、`pmod`、`pdiv`、`reverse` を使う。どれも `src/cryptol/` のもので、書き下したものはない（[cryptol-prelude.ja.md](../cryptol-prelude.ja.md)）。

## 実装層と証明の連鎖

### ディスパッチ: 1 つの実装で 3 つの鍵長

省略。ディスパッチはない。
spec で `{k}` をもつ関数は同じ const `k` について generic で、`Key(k)` を要求する。そのため 1 つの実装が 3 つの鍵長を受け持ち、その証明も 1 つである（上の「型」を参照）。

### 実行可能な関数とその契約

[`aes_impl.rs`](../../src/aes/aes_impl.rs)。`x_times`、`dot`、`sub_byte`、`sub_word`、`rot_word`、`xor_word`、`rcon`、`expand_key::<k>`、`sub_bytes`、`shift_rows`、`mix_column`、`mix_columns`、`add_round_key`、`round`、それらの逆、`inv_round_prime`、`encrypt_block::<k>`、`decrypt_block::<k>`、`decrypt_block_prime::<k>`。
ブロックは `Block = [u8; 16]`、ワードは `AESWord = [u8; 4]` で、その view が spec のものである。
`expand_key` は NSA の Rust と同じく、最大の鍵のラウンド鍵 `[[u8; 16]; 15]` を返す。
spec が見るのは最初の `Nr k + 1` 個（`round_keys`）と、鍵の最初の `Nk k` 個のワード（`key_words`）である。Rust には長さが `k` の式である配列がないからである。
[`aes_impl/main.rs`](../../src/aes/aes_impl/main.rs): `encrypt::<k>` と `decrypt::<k>` は鍵の `k / 8` バイトとブロックを受け取り、`join_block(r@) == AES::<k>::Encrypt(join_key(key@), join_block(input@))` を保証する。

### Verus はコードから spec へどうたどり着くか

ラウンドのループの不変条件は、最初の `r` 個のラウンド鍵の上のラウンドの、prelude の `foldl_take` である。
ラウンド鍵が 1 つ増えれば、定義によってラウンドが 1 つ増える。そのため SPARK の crate の `*_Eq`、`Take_Eq`、`Snoc` の lemma は要らない。
`MixColumns` と `InvMixColumns` は `xTimes` だけで書き、`lemma_dot_column` と `lemma_dot_inverse_column` で `•` に対して証明する。
`InvMixColumnsStep` の 1 行目から 3 行目は、xor の並べ替えが要る（`lemma_xor_rotate`、`bit_vector`）。
S-box の表と `Rcon` は spec 関数なので、実行可能な `S_BOX`、`INV_S_BOX`、`rcon` をそれと等しいと証明する。
`main_lemmas::lemma_split_join_key` が、鍵のバイトを spec の `split_key` に運ぶ。

## 確かめ方

### Verus: 実装 = spec、全入力で

上のすべての関数について、k = 128・192・256 のすべての鍵とブロックで。

### FFI での突き合わせ: 実行可能な関数を NSA の Cryptol と、テストで

[`cryptol/Verus/AES/`](../../cryptol/Verus/AES): `xTimes`、`•`、S-box、`Rcon` は全数。ラウンドの変換は 10,000 回。鍵スケジュールとブロック暗号は鍵長ごとに 1,000 回。`encrypt` と `decrypt` は合成したものと全体。FIPS 197 の Appendix A から C。
SPARK の crate の、spec 関数についての性質に当たるものはない（[ffi.ja.md](../ffi.ja.md)）。

### SAW: bitcode と MIR = NSA の Cryptol、k = 128・192・256 で

[saw.ja.md の「AES」](../saw.ja.md#aes): 上のすべての実行可能な関数を、末端から `main::encrypt` と `main::decrypt` まで、3 つの鍵長で、LLVM bitcode と MIR の上で、Cryptol に対して証明する。
AES のサイズはこの 3 つしかないので、これは実行可能な関数についての全入力での証明である。

### 何を証明し、何をテストしただけか

全入力で証明したこと: 実行可能な関数が spec 層と等しいこと（Verus）、NSA の Cryptol と等しいこと（SAW、3 つの鍵長で）。
証明していないこと: spec 層が NSA の Cryptol と等しいこと。これは読むこと、証明し直した性質、実行可能な関数を通して確かめる。
実行時間も証明していない。S-box は鍵と状態のバイトを添字にした表引きで、SPARK の crate の `main` と同じである（SPARK 版の定数時間のブランチに当たるものはない）。

## spec と実装が 1 対 1 でない箇所

[proving.ja.md](../proving.ja.md#spec-と実装が-1-対-1-でない箇所) と同じ。
`affine` と `inverse` には実行可能な対応物がない。`sub_byte` は表を引き、`SBoxCorrect` がその表を `affine` と等しいと証明する。
