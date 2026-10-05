#!/bin/bash
# 雙擊這個檔案，就會：建置 Lean 專案 → 檢查所有證明（不能有 sorry、只能用三個標準公理）
# → 跑當機測試 → 開啟結果網頁。給初學者看的中文流程。
cd "$(dirname "$0")" || exit 1

echo "=============================================="
echo " crashproof：證明「不會掉資料」的日誌"
echo "=============================================="

# 找得到 lake（Lean 的建置工具）嗎？
if ! command -v lake >/dev/null 2>&1; then
  if [ -x "$HOME/.elan/bin/lake" ]; then
    export PATH="$HOME/.elan/bin:$PATH"
  else
    echo "找不到 lake。請先安裝 Lean 4（elan）：https://leanprover.github.io"
    echo "按 Enter 關閉"; read -r _; exit 1
  fi
fi

echo
echo "[1/4] 建置 Lean 專案（第一次會比較久，要下載 Lean）..."
lake build || { echo "建置失敗"; read -r _; exit 1; }

echo
echo "[2/4] 檢查證明：不能有 sorry，主要定理只能依賴 propext / Classical.choice / Quot.sound"
./scripts/check-proofs.sh || { echo "證明檢查沒過"; read -r _; exit 1; }

echo
echo "[3/4] 跑當機測試：隨機在寫入途中斷電，看回復後資料對不對（固定亂數種子）"
python3 harness/crashtest.py --runs 300 --jobs 4 || { echo "當機測試失敗"; read -r _; exit 1; }

echo
echo "[4/4] 產生並打開結果網頁 docs/results.html"
mkdir -p out
./scripts/check-proofs.sh > out/axioms.txt 2>&1 || true
python3 harness/crashtest.py --runs 2000 --quiet --json out/crashproof.json || true
python3 scripts/make_results.py || true
open docs/results.html 2>/dev/null || echo "請手動打開 docs/results.html"

echo
echo "全部完成。這個視窗可以關掉了。"
read -r _
