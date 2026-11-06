# ペタショック化のアルゴリズムと形式証明

将棋AIの定跡に記録された評価値を、末端から手前へ伝える「ペタショック化」についての論文と、Lean 4による形式証明です。通常の千日手と連続王手の千日手を含む定跡を対象とします。

## 論文

- [主論文：ペタショック化アルゴリズム](paper/peta-shock-thesis.pdf)（[Typstソース](paper/peta-shock-thesis.typ)）
- [補足：最短保証脱出と距離最適化](paper/distance-optimization-supplement.pdf)（[Typstソース](paper/distance-optimization-supplement.typ)）

補足論文は、安全な候補手を前提とした距離最適化を扱うもので、主論文のdepth方式が最短脱出を保証するという主張ではありません。

## 証明の範囲

Leanでは、論文で定義した有限グラフ上のモデルと手続きについて、前提のもとで評価値の保証、千日手を考慮した指し手の安全性、選択手に沿ったdepthの再構築などを証明しています。末端に与える評価値の正確さや、定跡に登録されていない指し手については保証しません。

やねうら王のC++実装は、このモデルとの対応を点検・テストしていますが、C++実装全体をLeanで形式検証したわけではありません。双方連続王手による同一局面反復の不可能性は、抽象モデルでは入力条件として扱い、将棋の駒の動きからLeanで再証明したものではありません。

## Leanで検証する

Leanのバージョンは [lean/lean-toolchain](lean/lean-toolchain) に固定しています。Leanのバージョン管理ツール `elan` と `lake` が使える環境で、リポジトリのルートから次を実行します。

```sh
cd lean
lake build
lake env lean PaperClaims.lean
lake env lean DistancePaperClaims.lean
lake env lean Audit.lean
```

- [PaperClaims.lean](lean/PaperClaims.lean)：主論文の定理番号とLeanの定理名の対応を確認する入口。
- [DistancePaperClaims.lean](lean/DistancePaperClaims.lean)：補足論文の定理の確認用。
- [Audit.lean](lean/Audit.lean)：定理の依存する公理の確認用。
- [PetaProof/](lean/PetaProof/)：定義、証明、検証用の例。

GitHub Actionsでも、pushとpull requestのたびに同じ検証を実行する設定を用意しています。

`#check` はLeanの命題型を確認するものであり、論文の自然言語による記述との対応を自動で証明するものではありません。定理の前提も含めて確認してください。

## 論文のビルド

Typstと日本語フォントを用意し、リポジトリのルートから実行します。

```sh
typst compile paper/peta-shock-thesis.typ
typst compile paper/distance-optimization-supplement.typ
```

フォント環境やTypstのバージョンにより、PDFの見た目や改ページが異なる場合があります。

## ライセンス

ライセンスは未決定です。利用条件を定める前に公開する場合は、この点をご確認ください。
