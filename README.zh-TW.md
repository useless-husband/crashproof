# crashproof（證明不掉資料的日誌）

**一個「寫入前日誌」（write-ahead log），它的「斷電不掉資料」是用 Lean 4 *證明* 出來的——
接著把編譯出的程式拿去當機測試，驗證它符合被證明的模型，再跟另一個獨立寫成的日誌
（wren-os）做差異比對。** 這是把 MIT FSCQ 的想法用另一套證明工具重做的**學習專案**，與 MIT
無關，也不宣稱任何原創。

測試只能找到 bug，永遠無法證明儲存層「絕對不會掉已提交的資料」——斷電可以發生在多到數不完
的任一瞬間。證明可以。crashproof 先精確定義「帶寫入快取的硬碟在斷電時可能發生什麼」，實作
一個日誌，然後證明（沒有任何 `sorry`，只用 Lean 的三個標準公理）：任何斷電與回復之後，資料
要嘛完整存在、要嘛完全沒發生，絕不會停在寫一半。

```
$ crashproof demo
...（斷電發生在安裝到一半：區塊 1 已是新值、區塊 0 還是舊值）
after recovery (the header commits the transaction, so the log is replayed):
header empty
0 3
1 4
```

因為斷電發生在「成交點」之後，回復會重播日誌，交易原子地完成。

## 證明了什麼

CI 會用 `#print axioms` 確認每條定理只依賴 `propext`、`Classical.choice`、`Quot.sound`：

| 定理 | 白話 |
|---|---|
| `atomicity` | commit 中任一點斷電再回復，邏輯磁碟會停在交易前或交易後，不會在中間。 |
| `durability` | commit 一回傳，結果就是交易後的狀態，之後任何斷電+回復都重現它。 |
| `recovery_idempotent` | 回復途中斷電幾次都行，只要有一次回復做完，結果仍是允許的狀態。 |
| `get_correct` | 交易中讀取會看到自己這筆交易的寫入，其餘位置看到已提交的值。 |
| `put_correct`, `put?_ok` | 一次寫入只改一個邏輯區塊；`put?` 只會建出放得進日誌的交易。 |
| `commitAll_spec` | 一連串交易中斷電，會回復到某個前綴的狀態，不會出現改到一半的交易。 |
| `commit_spec`, `recover_spec` | 以上所根據的完整 Crash Hoare 規格。 |

定理白話、公理報告與當機測試統計，整理在 [`docs/results.html`](docs/results.html)。

## 運作原理

- **硬碟模型**（`Crashproof/Disk.lean`）：每個區塊有「目前值」加上「上次 sync 以來寫過的舊
  值」；`write` 只進快取、`sync` 是屏障、斷電時每個區塊各自停在任一殘存值，正在寫的區塊可
  能在 512 位元組磁區邊界被撕裂。這就是 FSCQ/xv6 的非同步硬碟模型。
- **Crash Hoare Logic**（`Crashproof/Prog.lean`）：程式是 free monad，語意允許在任一步前斷
  電；規格是「前置／後置／**斷電**」三種條件，沿用 FSCQ 的做法。
- **日誌**（`Crashproof/Log.lean`）：標頭＋日誌槽＋安裝＋清除，屏障寫明；協定形狀與 wren-os
  的 `kernel/log.c` 相同。
- **真實區塊**（`Crashproof/Block.lean`）：4096 位元組 `ByteArray` 編解碼，證明了往返與耐撕
  裂兩條定律，讓定理適用於執行檔真正寫入的位元組。
- **可執行程式**（`App/`、`native/dev.c`、`Main.lean`）：直接「執行」定理所描述的那些 `Prog`
  值，操作磁碟映像檔，內建模擬寫入快取與斷電注入。

完整說明見 [`docs/report.md`](docs/report.md)，架構見 [`docs/DESIGN.md`](docs/DESIGN.md)，給
初學者的中文導讀見 [`docs/導讀.zh-TW.md`](docs/導讀.zh-TW.md)。

## 實測結果（在本機量測）

Apple M 系列、共用機器；固定亂數種子，失敗時印出。

- **證明**：乾淨建置、無 `sorry`、只用三個標準公理（`make proofs`）。
- **當機測試**：inject／torn／kill 三種斷電共 2000/2000 次回復到允許狀態，且回復途中再注入
  斷電（`make harness`）。
- **突變測試**：6/6 個一行證明突變無法編譯；7/7 個壞掉協定被當機測試抓到（`make mutants`）。
- **與 wren-os 差異比對**：wren-os 的 `kernel/log.c` 原封不動編譯，通過同一套當機測試
  2000/2000（`make diff-wren`）。唯一可觀察到的協定差異（wren-os 用 CRC 取代最後一次屏障）
  在 `docs/report.md` §7 與 `wren/reproduce.sh` 重現與評估。那不是 bug。

## 限制

- **可信基礎**未被證明：Lean 編譯器、`native/dev.c`、作業系統與硬碟韌體。模型假設 flush 誠
  實、屏障是真正的柵欄。當機測試負責打這塊，證明不涵蓋它。
- 還沒在上面做檔案系統或鍵值層。`commitAll_spec` 是它的基礎，這部分是因時間略過，不是造假。
- 併發只建模成「交易依序進行」（`commitAll_spec`）；執行檔是單執行緒。

## 建置與測試

需要 Lean 4（用 [elan](https://leanprover.github.io)，版本鎖在 `lean-toolchain`）與
Python 3。在本資料夾內執行（資料夾名含空白與中文，所有建置路徑皆為相對路徑）：

```sh
make build        # 編譯函式庫與執行檔
make proofs       # 無 sorry；只用 propext / Classical.choice / Quot.sound
make test         # build + proofs + 當機測試
make demo         # 上面那段示範
make mutants      # 證明與當機測試的突變檢查
make diff-wren    # 與 wren-os 差異比對（需 wren-os 倉庫放在同層）
make results      # 重新產生 docs/results.html
```

或直接雙擊 **`跑跑看.command`**（中文、適合初學者：建置、檢查證明、跑當機測試、開結果網頁）。

## 相關研究

- **FSCQ**（Chen 等，SOSP 2015）——本專案學習的對象，提出 Crash Hoare Logic。**DFSCQ**
  （SOSP 2017）加入 log-bypass 與精確的 fsync 規格。
- **Yggdrasil**（OSDI 2016）——用 SMT「按鈕式」驗證崩潰一致性，而非互動式證明。
- **Perennial**（SOSP 2019）——以 Coq/Iris 處理併發崩潰安全，遠超本專案的循序日誌。
- **xv6 的 log**——crashproof 與 wren-os 都遵循的教學用 redo log。
- **wren-os**（`github.com/useless-husband/wren-os`）——作者從零寫的作業系統；其
  `kernel/log.c` 是此處差異比對的對象，僅唯讀使用、未修改。
- **linproof**（`github.com/useless-husband/linproof`）——作者先前的 Lean 專案（可線性化檢查
  器，附正確性證明）；相同工具鏈與 CI 慣例。

本專案是對已發表想法的學習重製，不宣稱原創，也與上述作者無隸屬關係。

## 授權

MIT，見 [LICENSE](LICENSE)。
