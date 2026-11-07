# カバレッジとミューテーションテスト

[English](coverage.md) | 日本語

FFI の性質が実行可能なコードのどれだけを動かすか: LLVM のソースベースのカバレッジ（rustc の `-C instrument-coverage`）を、region・行・分岐の結果ごとに測る。
SPARK の crate の `spark/doc/coverage.md`（github.com/manthonyaiello/Foundation、タグ `spark-v1.0`。GNATcoverage で測っている）の「Coverage」の部分に対応する。
また[ミューテーションテスト](#ミューテーションテスト)では、どの欠陥を性質・Verus・SAW が捕まえるかを扱う。[README](../README.ja.md) へ戻る。

**MC/DC はない。**
SPARK の crate は文・判定・MC/DC を測る（`--level=stmt+mcdc`）。
この crate は MC/DC を測らない。rustc に測れないからである。MC/DC の計装は取り除かれ、Rust 1.98.1（固定したツールチェーン）も nightly の 1.96 と 1.101 も、`-Zcoverage-options` に `block`・`branch`・`condition` しか受けつけない。
代わりに測るもの:

| SPARK（gnatcov） | ここ（llvm-cov） |
|---|---|
| 文 | region: rustc のコードの region（1 つのカウンタが受け持つコードのひと続き）。行も |
| 判定 | 分岐の結果: 各 `if`・`while`・`match` の腕の真と偽の側（`branch`）と、`&&` と `\|\|` の各オペランドの真と偽の側（`condition`） |
| MC/DC | **なし** |

条件カバレッジ（`&&` と `||` の各オペランドの両側）は MC/DC より弱い。各オペランドが単独で判定の結果を変えることを示せとは求めないからである。

## 実行

`scripts/check-coverage.sh` は、`cryptol/properties.txt` のすべての性質のもとで、`coverage/units.txt` のファイルを測る。
対象は、実行可能な関数（`aes/aes_impl.rs`、`aes/aes_impl/main.rs`、`sha2/sha256_stream.rs`、`hmac/sha256_impl.rs`）、`sha2/functions.rs` と `sha2/notation.rs` の exec の対応物、FFI エクスポート `ffi/*.rs` である。
spec 層は対象外である。`cargo build` はすべての `spec fn`・`proof fn`・proof ブロック・アサーション・ループ不変条件を消去するので、カバーすべきコードがない。SPARK の crate の Ghost コードが `-gnata` なしではコードをもたないのと同じである。

```console
$ PATH=<cryptol-3.6.0>/bin:$PATH scripts/check-coverage.sh   # すべての性質
$ scripts/check-coverage.sh prop_Impl_Dot                     # 部分的な報告
```

必要なものは、ツールチェーンの `llvm-tools` コンポーネント（`rustup component add llvm-tools --toolchain 1.98.1`。rustc 自身の LLVM の `llvm-profdata` と `llvm-cov` でないとプロファイルを読めない）と、`check-ffi.sh` が必要とするもの。
スクリプトは次のことをする:

1. FFI のライブラリ（`ffi/`）を計装つきで `target/cov/` にビルドする。
   プロファイルは FFI での突き合わせのもの（release、オーバーフローの検査、debug assertion）で、`RUSTFLAGS="-C instrument-coverage -Zcoverage-options=branch,condition"` をつける。
   分岐のオプションは unstable なので、nightly に切り替えずに、固定した 1.98.1 で `RUSTC_BOOTSTRAP=1` を設定してビルドする。測るのは固定した rustc がコンパイルするコードである。
   これをするのはこのビルドだけで、crate のビルド、証明、FFI での突き合わせのライブラリには触れない。
2. そのライブラリに対して `check-ffi.sh` を回す（`FFI_LIB`、`FFI_OUT`）。すべての性質をいつもどおりに判定する。
3. プロファイルをまとめて `target/cov/report/` に置く:
   `summary.txt`（ファイルごとの表と、すべての違反とその説明。`scripts/coverage-summary.py` が作る）、
   `report.txt`（llvm-cov のファイルごと・関数ごとの報告）、
   `html/`（注釈つきのソース。分岐の回数つき）、
   `export.json`。
4. clean な tree からすべての性質を回したときは、`coverage/results.txt`（コミット、日付、道具、表）を書く。
   SPARK の crate は数字を CI に置いているが、この crate には CI がない。

**Cryptol のプロセスからのプロファイル。**
ライブラリは LLVM のプロファイルの runtime をもっていて、Cryptol がライブラリを読み込むと自分の終了ハンドラを登録する。
そのため各 `cryptol -b`（性質 1 つにつき 1 つ）は、終了するときに自分のプロファイルを `target/cov/traces/` に書く（`LLVM_PROFILE_FILE`、pid ごとに 1 ファイル）。
SPARK の crate はこのために専用のユニット（`coverage/foundation_spark_coverage`。gnatcov の dump を `atexit` で登録する）が要るが、この crate には要らない。
実行ごとにプロファイルが 1 つなければ、スクリプトは失敗する。
ビルドの中で計装される道具（proc macro、build script）もプロファイルを書くが、それは `target/cov/build-prof/` に行き、使わない。

**generic な関数。**
generic な関数は具体化ごとに記録をもつ（`encrypt_block::<128>`、`::<192>`、`::<256>`）。
region や分岐の結果は、どれかの具体化が通ればカバーされたとし、ソースの位置で 1 回だけ数える。

**数えないもの。**
マクロの展開の中の分岐は、ファイルの中に region をもたない。単一の条件の `assert!` の失敗する側は数えないが、その中の `&&` や `||` の各オペランドは数える。
オーバーフローと範囲の検査はコンパイラが挿入するもので、ソースの分岐ではないので、分岐としては数えない（検証したコードでは、その失敗する側は証明が排除している）。

## 説明するか、閉じるか

違反（一度も実行されない region、一度も取られない分岐の結果）はすべて、`coverage/explained.txt` の項目（ファイル、行の前後の空白を除いたテキスト、理由）に一致しなければならない。一致しなければスクリプトは失敗する。
SPARK の crate と同じく、項目は性質が作りのうえで届かないコードのためのものである。狙ったテストの抜けは、性質を足して閉じる。
`src/` の下のファイルに計装されたコードがあるのに `units.txt` にない場合や、載っているファイルにそれがない場合にも、スクリプトは失敗する。そのため新しい実行可能なコードが気づかれずに測定から漏れることはない。

項目は、Cryptol の型がすでに保証していることを FFI エクスポートが実行時に確かめる部分である（`src/ffi/mod.rs`）:
`check_key_size` の後の `_ => unreachable!()` の腕（Cryptol の `Key k` は 128・192・256 しか許さない）、`check_key_size` 自身の最後のオペランド、HMAC の `k < MAX_BYTES && n < MAX_TEXT`（Cryptol の `61 >= width k`）。
SPARK の crate のエクスポートにはこうした確認がないので、そのファイルには項目がない。
実装層（`aes/`・`sha2/`・`hmac/`）には項目がない。性質がその全部を動かす。

2026-11-02 の測定:

| | region | 行 | 分岐 | MC/DC |
|---|---|---|---|---|
| 実装層と exec の対応物 | 947/947 | 692/692 | 80/80 | 測っていない |
| FFI エクスポート | 583/589 | 267/273 | 13/18 | 測っていない |
| 合計 | 1530/1536 | 959/965 | 93/98 | 測っていない |

違反は 11 個で、すべて FFI エクスポートにあり、説明がついている。

## ミューテーションテスト

カバレッジが示すのは FFI の性質がどのコードを動かすかであって、どの入力を試すかではない。
`scripts/mutation.py`（SPARK の crate の `spark/scripts/mutation.py` に当たる）はその差を測る。
[`mutation/mutants.txt`](../mutation/mutants.txt) の各ミュータントを checkout の作業用の写しに当て（checkout そのものには決して当てない）、何がそれを捕まえるかを記録する:

* **FFI**: 変異させた tree からビルドしたライブラリを、変異させたコードに届く性質に対して回す（最初の失敗で止める）。それを生き延びたものは、すべての性質に対して回す（`--full`）。
* **Verus**: 変異させたコードのモジュールに `cargo verus focus -- --verify-only-module M ...` をかける。
  失敗は、unproved（検証エラー: 事後条件・アサーション・ループ不変条件・事前条件・オーバーフローのどれかが証明できない）、timeout（リソース上限 rlimit に達しただけ。反証ではない）、nocompile に分ける。
  Verus は反例を出さないので、SPARK の列の "refuted" に当たるものはない。
* **SAW**: ミュータントごとに `check-saw.sh --print`。`SAW_ROUTE` で指定しなければ両方の経路（LLVM と MIR）。

```console
$ scripts/mutation.py check                      # すべてのミュータントが当たる
$ scripts/mutation.py setup /tmp/mut             # 作業用の写し
$ scripts/mutation.py ffi /tmp/mut --baseline    # 対照:
$ scripts/mutation.py prove /tmp/mut --baseline  #   変異させていない tree は通る
$ scripts/mutation.py ffi /tmp/mut               # すべてのミュータント
$ scripts/mutation.py ffi /tmp/mut --full        # 生き延びたもの: すべての性質
$ scripts/mutation.py prove /tmp/mut             # すべてのミュータント
$ scripts/mutation.py saw /tmp/mut --baseline
$ scripts/mutation.py saw /tmp/mut ID ...        # 生き延びたものと F*
$ scripts/mutation.py report /tmp/mut            # 表を Markdown で
```

必要なものは、`check-ffi.sh` と `check-saw.sh` が必要とするものと、`cargo verus`（`PATH` に置くか `CARGO_VERUS` で指定）。
`witness` は、性質が試さない入力でミュータントに対して Cryptol の `:check` を 1 回回す。`diagnose` は、ミュータントに対して引数を増やして（`--rlimit` を大きくして）Verus をもう一度回す。どちらも診断用で、列には入らない。

**ミュータント。**
SPARK の crate の 84 個の欠陥を同じ id で使い、それぞれ SPARK の行と同じことをする Verus の行に書いた。
`aes/aes_impl.rs` に 34 個（A）、`aes/aes_impl/main.rs` に 5 個（M）、`sha2/sha256_stream.rs` に 26 個（S）、`hmac/sha256_impl.rs` に 9 個（H）、`sha2/functions.rs` に 14 個（F）で、全部で 88 個。
SPARK の一覧との違い:

* S27–S29 は除いた。メッセージの配列を `'First` からでなく 0 から添字で引く欠陥で、Rust のスライスはいつも 0 から始まるので、この欠陥は書けない。
* A29 は、SPARK の一覧では鍵スケジュールの初期化を落とす。
  Rust は初期化していない配列を読ませないので、ここではスケジュールを 0 でなく 1 で初期化する。
  どのワードも読む前に書かれるので、SPARK のミュータントと同じく等価である。
* F01–F07 は 2 通りに書いた。
  SPARK の crate では `SHA2.Functions` を spec と実装で共有しているので、1 つのミュータントが両方を変える。
  ここでは spec 関数と exec の対応物が別の関数なので（Verus は `spec fn` を実行できない）、`F01a`–`F07a` は exec の対応物だけを変え、`F01b`–`F07b` は SPARK のミュータントと同じく両方を同じように変える。
  これが、2 行以上にわたる唯一の種類のミュータントである。

**判定。**
最後の列は、FFI と Verus のどちらがミュータントを捕まえるかを示す: 両方、FFI だけ、Verus だけ（Verus が時間切れになっただけのときは "(rlimit)" をつける）、どちらでもない。
SPARK のスクリプトは FFI が捕まえれば "FFI" とし、証明も捕まえるかは記録しない。
この列はそれも示す。F01a–F07a と F01b–F07b の違いがちょうどそこにあるからである。

### 結果

2026-11-03 に x86_64 の Linux マシン（Intel Core i9-9900K）で回した。
対照は通る: 変異させていない tree は、ミュータントが届く 72 個の性質に合格し、Verus はミュータントが触れる 18 個のモジュールを検証し（145 verified、26 秒）、SAW は変異させていない実装を両方の経路で証明する（168 件の証明。陰性対照 16 件は失敗する。934 秒）。

FFI は 88 個のうち 73 個を殺す。
生き延びた 15 個はどれもすべての性質に合格する（`--full`）。そのうち 10 個は等価なミュータント（A20、A29、A33、M04、S08、S10、S12、S14、S25、S26）である。
5 個はストリーミングの SHA-256 の長さの符号化にある本物のバグ（S20–S24）で、性質が試すより長いメッセージでしか現れない（S24 は 4 KiB から、S21 は 2^53 バイトから）。
これは SPARK の crate で生き延びたものから、6 個目の本物のバグ S27 を除いたものである。S27 はここに対応するものがない。

Verus は 5 個の本物のバグすべてで失敗する。`finalize` の長さの符号化のループ不変条件で（4 個は事前条件でも）、どれも検証エラーによる。gnatprove は SPARK の crate のものを時間切れで失敗させている。
FFI が殺す 73 個のうち、Verus は 66 個で失敗する。62 個は検証エラーで、4 個（A25、A27、A28、M03）はリソース上限に達してである。
残る 7 個は F01b–F07b で、Verus はこれを証明する。gnatprove が SPARK の crate の F01–F07 を証明するのと同じで、実装は同じく変異させた spec に対して証明される。
exec の対応物だけを変える F01a–F07a では、Verus は失敗する。

等価なミュータント 10 個のうち、Verus は 4 個（A29、A33、S12、S26）を証明し、M04 で時間切れになり、残る 5 個（A20、S08、S10、S14、S25）で失敗する。コードはなお契約を満たしているにもかかわらずである。
Verus の失敗は通らなかった証明であって、見つかったバグではない。

SAW（両方の経路、`mutation.py saw`）は 29 個のミュータントに回した。FFI を生き延びた 15 個と、F のミュータント 14 個である。

* 等価なミュータント 10 個のうち 9 個を証明する。
  M04（InvCipher の代わりに InvCipher'）は止まらない。
  LLVM の経路の k = 128 での `main::decrypt` の証明は、`decrypt_block_prime` を証明済みの `InvCipher'` の契約で置き換えるが、Main.cry の `Decrypt`（InvCipher）に対するゴールを、`mutation.py` が許す 1 時間のうちに終えない。
  SPARK の crate の SAW は M04 を証明し、S14 で失敗する。S14 はここでは SAW が証明する。
* 5 個の本物のバグはすべて通してしまう。SPARK の crate と同じで、ハッシュの証明は 200 バイト以下の固定の長さで行っているからである。
  3 つのうちでこれを拒むのは Verus だけである。
* F01 と F07 を（a も b も。SAW が読むのは exec のコードで、両者で共通である）反例つきで拒む。F02（Maj）は rme のもとで 10G のメモリ上限で拒む。SPARK の crate の SAW と同じである。
  F03–F06 は LLVM のスクリプトを未束縛の名前で止める。ミュータントは、スクリプトが最初に検証する const generic の具体化（`ROTR::<13>`、`SHR::<3>`、`SHR::<10>`、`ROTR::<25>`）をもう呼ばないので、rustc がその関数を出さないのである。
  列ではこれを失敗ではなく `error` として記録する。
