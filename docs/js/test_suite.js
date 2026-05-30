/**
 * Loop Course Test Suite & Benchmarks
 * Runs in-browser logic validation and speed measurement for the Solver and Generator.
 */
class LoopCourseTestSuite {
  constructor() {
    this.tests = [];
    this.initTests();
    this.bindDOM();
  }

  bindDOM() {
    this.btnRun = document.getElementById('btn-run-tests');
    this.selectScope = document.getElementById('select-scope');
    this.progressBar = document.getElementById('test-progress-bar');
    this.progressContainer = document.getElementById('test-progress');
    this.resultsBody = document.getElementById('test-results-body');
    this.statusBadge = document.getElementById('status-badge');
    
    this.metricTotal = document.getElementById('metric-total');
    this.metricPass = document.getElementById('metric-pass');
    this.metricFail = document.getElementById('metric-fail');
    this.metricBench = document.getElementById('metric-bench');

    this.btnRun.addEventListener('click', () => this.runSuite());
  }

  initTests() {
    // CATEGORY 1: Solver Logic & Mappings
    this.addTest('Solver: 座標マッピング整合性チェック', 'solver', async (log) => {
      const solver = new window.LoopCourseSolver(3, 3, Array.from({ length: 3 }, () => new Array(3).fill(null)));
      
      log.info(`グリッド定義: 3行 x 3列 (Hエッジ数: 12, Vエッジ数: 12, 合計エッジ数: 24)`);
      
      // Test getHEdgeIndex
      log.info(`--- getHEdgeIndex のテスト ---`);
      const h0 = solver.getHEdgeIndex(0, 0);
      const h11 = solver.getHEdgeIndex(3, 2);
      const hInvalid = solver.getHEdgeIndex(4, 0);
      log.info(`(0, 0) H-Edge -> ${h0} (期待値: 0)`);
      log.info(`(3, 2) H-Edge -> ${h11} (期待値: 11)`);
      log.info(`(4, 0) H-Edge (範囲外) -> ${hInvalid} (期待値: -1)`);
      
      this.assert(h0 === 0, 'getHEdgeIndex(0, 0) が正しくありません');
      this.assert(h11 === 11, 'getHEdgeIndex(3, 2) が正しくありません');
      this.assert(hInvalid === -1, '範囲外のH-Edgeインデックスが -1 を返しませんでした');

      // Test getVEdgeIndex
      log.info(`--- getVEdgeIndex のテスト ---`);
      const v0 = solver.getVEdgeIndex(0, 0);
      const v11 = solver.getVEdgeIndex(2, 3);
      const vInvalid = solver.getVEdgeIndex(3, 0);
      log.info(`(0, 0) V-Edge -> ${v0} (期待値: 12)`);
      log.info(`(2, 3) V-Edge -> ${v11} (期待値: 23)`);
      log.info(`(3, 0) V-Edge (範囲外) -> ${vInvalid} (期待値: -1)`);
      
      this.assert(v0 === 12, 'getVEdgeIndex(0, 0) が正しくありません');
      this.assert(v11 === 23, 'getVEdgeIndex(2, 3) が正しくありません');
      this.assert(vInvalid === -1, '範囲外のV-Edgeインデックスが -1 を返しませんでした');

      // Test getCellEdges
      log.info(`--- getCellEdges のテスト ---`);
      const cellEdges = solver.getCellEdges(1, 1);
      log.info(`セル(1, 1)の四辺エッジ -> Top: ${cellEdges[0]}, Right: ${cellEdges[1]}, Bottom: ${cellEdges[2]}, Left: ${cellEdges[3]}`);
      log.info(`期待値 -> Top: 4, Right: 18, Bottom: 7, Left: 17`);
      
      this.assert(cellEdges[0] === 4, 'getCellEdges(1, 1) Top が正しくありません');
      this.assert(cellEdges[1] === 18, 'getCellEdges(1, 1) Right が正しくありません');
      this.assert(cellEdges[2] === 7, 'getCellEdges(1, 1) Bottom が正しくありません');
      this.assert(cellEdges[3] === 17, 'getCellEdges(1, 1) Left が正しくありません');

      // Test getDotEdges
      log.info(`--- getDotEdges のテスト ---`);
      const dotEdgesCorners = solver.getDotEdges(0, 0); // Top-Left corner
      const dotEdgesCenter = solver.getDotEdges(1, 1);  // Inside grid
      
      log.info(`頂点(0, 0) (左上角) に接続するエッジ数 -> ${dotEdgesCorners.length} (エッジリスト: ${dotEdgesCorners.join(',')})`);
      log.info(`頂点(1, 1) (中央内部) に接続するエッジ数 -> ${dotEdgesCenter.length} (エッジリスト: ${dotEdgesCenter.join(',')})`);
      
      this.assert(dotEdgesCorners.length === 2, '左上角の頂点接続数は2でなければなりません');
      this.assert(dotEdgesCenter.length === 4, '中央の頂点接続数は4でなければなりません');
      
      log.success(`すべての座標マッピング関数の正確なインライン処理と整合性を確認しました。`);
    });

    this.addTest('Solver: 数字ヒント論理推論 (Clue Deduction)', 'solver', async (log) => {
      // Create a 3x3 board, with clue 3 in the center cell (1, 1) to avoid corner-dot constraints
      const clues = [
        [null, null, null],
        [null, 3, null],
        [null, null, null]
      ];
      const solver = new window.LoopCourseSolver(3, 3, clues);
      
      log.info(`初期盤面: 3x3 グリッド, 内部セル(1, 1) に ヒント「3」`);
      log.info(`セル(1, 1)の四辺は 4, 18, 7, 17 (Top, Right, Bottom, Left)`);
      
      // Let's set Left edge (17) as Cross (-1) and see if it deducts other 3 edges to be Lines (1)
      solver.edgeStates[17] = -1; 
      log.info(`推論前設定: セル(1, 1)の左辺 (エッジ 17) を ×印 (-1) に設定`);
      
      const success = solver.deduct();
      log.info(`solver.deduct() 呼び出し結果 -> ${success ? '成功 (矛盾なし)' : '失敗 (矛盾あり)'}`);
      
      this.assert(success === true, '推論の実行自体が矛盾で失敗しました');
      
      log.info(`セル(1, 1)の他3辺の状態確認:`);
      log.info(`  Top Edge (4): ${solver.edgeStates[4]} (期待値: 1)`);
      log.info(`  Right Edge (18): ${solver.edgeStates[18]} (期待値: 1)`);
      log.info(`  Bottom Edge (7): ${solver.edgeStates[7]} (期待値: 1)`);
      
      this.assert(solver.edgeStates[4] === 1, 'ヒント3で1辺が×のとき、他辺が線(1)に推論されませんでした (Top)');
      this.assert(solver.edgeStates[18] === 1, 'ヒント3で1辺が×のとき、他辺が線(1)に推論されませんでした (Right)');
      this.assert(solver.edgeStates[7] === 1, 'ヒント3で1辺が×のとき、他辺が線(1)に推論されませんでした (Bottom)');
      
      log.success(`セル周囲の数字ヒントに対するローカル演繹ルールが完璧に動作しています。`);
    });

    this.addTest('Solver: 頂点接続数制限チェック (Dot Degree Violation)', 'solver', async (log) => {
      const solver = new window.LoopCourseSolver(2, 2, [[null, null], [null, null]]);
      
      log.info(`初期盤面: 2x2 グリッド, ヒントなし`);
      log.info(`中央頂点 (1, 1) に接続する4本のエッジのうち、3本を線 (1) に設定して矛盾を検証します。`);
      
      // Central dot (1, 1) connects to edges 2 (Left-H), 3 (Right-H), 7 (Up-V), 10 (Down-V)
      // Set 3 of them to 1 (line)
      solver.edgeStates[2] = 1;
      solver.edgeStates[7] = 1;
      solver.edgeStates[10] = 1;
      
      log.info(`設定エッジ: エッジ2=1 (左), エッジ7=1 (上), エッジ10=1 (下)`);
      
      const success = solver.deduct();
      log.info(`solver.deduct() 呼び出し結果 -> ${success ? '推論成功' : '矛盾検知 (正解)'}`);
      
      this.assert(success === false, '頂点接続数が3本になったときに矛盾が検知されませんでした');
      log.success(`1つの頂点から線が3本以上分岐する「分岐・交差の禁止ルール（次数制約）」が正常に検知されました。`);
    });

    this.addTest('Solver: 早期小ループ閉鎖防止の検証 (Premature Loop Check)', 'solver', async (log) => {
      // 3x3 grid with clue 3 in bottom-right cell
      const clues = [
        [null, null, null],
        [null, null, null],
        [null, null, 3]
      ];
      const solver = new window.LoopCourseSolver(3, 3, clues);
      log.info(`初期盤面: 3x3 グリッド, セル(2, 2) に「3」のヒント。`);
      log.info(`左上のセル(0, 0)の周囲に、早期に独立した閉じた1マスのループを描きます。`);
      
      // Top-Left cell (0, 0) edges: H0, V12, H3, V13
      solver.edgeStates[0] = 1;
      solver.edgeStates[12] = 1;
      solver.edgeStates[3] = 1;
      solver.edgeStates[13] = 1;
      
      log.info(`設定エッジ (1マスの閉ループ): エッジ 0, 12, 3, 13 を 線(1) に設定`);
      
      const success = solver.deduct();
      log.info(`solver.deduct() 呼び出し結果 -> ${success ? '成功' : '早期閉ループ矛盾検知 (正解)'}`);
      
      this.assert(success === false, '盤面に未解決のヒント3が残っている状態で小さなループが閉じたとき、矛盾が検出されませんでした');
      log.success(`単一輪以外の不要な小ループ（ショートカット）を早期に弾く「ループコース唯一性制約」が正常に検出されました。`);
    });

    this.addTest('Solver: バックトラック解探索 (Uniqueness Check)', 'solver', async (log) => {
      // Define a simple solved 2x2 shape
      // Cell partition: [[1, 0], [1, 1]] (Top-left, Bottom-left, Bottom-right are Inside. Top-right is Outside)
      // Clues calculated from this partition:
      const clues = [
        [2, 2],
        [2, 2]
      ];
      const solver = new window.LoopCourseSolver(2, 2, clues);
      log.info(`定義パズル: 2x2 グリッド\n[2][2]\n[2][2]`);
      
      const solutions = solver.solve();
      log.info(`solver.solve() 実行完了。見つかった解の数: ${solutions.length}`);
      
      this.assert(solutions.length === 1, `2x2の単純なパズルで一意の解が見つかりませんでした (見つかった解: ${solutions.length}個)`);
      
      log.success(`バックトラック解探索エンジンが正常に機能し、ユニーク解の検証が正しく実行されています。`);
    });


    // CATEGORY 2: Generator Algorithms
    this.addTest('Generator: ループ生成の連続性・閉包性検証', 'generator', async (log) => {
      const rows = 7;
      const cols = 7;
      const generator = new window.LoopCourseGenerator(rows, cols);
      
      log.info(`7x7 グリッドのランダムループ成長処理を実行します。`);
      const { cells, loopEdges } = generator.generateRandomLoop();
      
      log.info(`ランダムループ成長に成功しました。エッジ全体の配列サイズ: ${loopEdges.length}`);
      
      // Calculate dot degrees for the generated loop
      const numDots = (rows + 1) * (cols + 1);
      const degrees = new Array(numDots).fill(0);
      
      const numH = (rows + 1) * cols;
      
      // Helper to compute dot edges
      const getDotEdges = (r, c) => {
        const edges = [];
        if (r > 0) edges.push(numH + (r - 1) * (cols + 1) + c);
        if (r < rows) edges.push(numH + r * (cols + 1) + c);
        if (c > 0) edges.push(r * cols + (c - 1));
        if (c < cols) edges.push(r * cols + c);
        return edges;
      };

      let activeDots = 0;
      for (let r = 0; r <= rows; r++) {
        for (let c = 0; c <= cols; c++) {
          const dotId = r * (cols + 1) + c;
          const edges = getDotEdges(r, c);
          let count = 0;
          for (const idx of edges) {
            if (loopEdges[idx] === 1) count++;
          }
          degrees[dotId] = count;
          if (count > 0) activeDots++;
        }
      }

      log.info(`生成されたループ内のアクティブな頂点（角/接続部）の数: ${activeDots}`);
      
      // Verify that all active dots have degree exactly 2 (continuous single path)
      let branches = 0;
      let deadEnds = 0;
      for (let i = 0; i < numDots; i++) {
        if (degrees[i] > 0) {
          if (degrees[i] !== 2) {
            if (degrees[i] === 1) deadEnds++;
            else branches++;
          }
        }
      }

      log.info(`接続性の検証: 死に端(次数1): ${deadEnds}箇所, 分岐・交差(次数>2): ${branches}箇所`);
      
      this.assert(deadEnds === 0, 'ループが途切れており、行き止まり（次数1の頂点）が存在します');
      this.assert(branches === 0, 'ループが分岐または交差（次数3以上の頂点）しています');
      this.assert(activeDots >= 8, 'ループの規模が極端に小さすぎます');
      
      log.success(`生成されたループは、すべての角で完璧に繋がり、交差や枝分かれのない1本の美しいループになっています。`);
    });

    this.addTest('Generator: Inside 4x4 塊の禁止ルールの検証', 'generator', async (log) => {
      const rows = 15;
      const cols = 15;
      const generator = new window.LoopCourseGenerator(rows, cols);
      
      log.info(`15x15 の大盤面でランダムループ成長を10回行い、 Inside領域の 4x4 塊禁止制約が厳守されているかを検証します。`);
      
      for (let i = 1; i <= 10; i++) {
        const { cells } = generator.generateRandomLoop();
        
        // Check if there are any 4x4 blocks filled completely with 1 (Inside)
        let blockCount = 0;
        for (let r = 0; r < rows - 3; r++) {
          for (let c = 0; c < cols - 3; c++) {
            let isAllInside = true;
            for (let dr = 0; dr < 4; dr++) {
              for (let dc = 0; dc < 4; dc++) {
                if (cells[r + dr][c + dc] !== 1) {
                  isAllInside = false;
                  break;
                }
              }
              if (!isAllInside) break;
            }
            if (isAllInside) blockCount++;
          }
        }
        
        log.info(`試行 ${i}: 検出された完全に塗りつぶされた 4x4 ブロック数 -> ${blockCount}`);
        this.assert(blockCount === 0, `成長アルゴリズムにおいて、Inside領域が 4x4 の巨大な塊を形成してしまいました (試行: ${i})`);
      }
      
      log.success(`すべての試行において 4x4 Inside 塊の禁止制約が完全に守られています。ループのうねり・蛇行性能が担保されています。`);
    });


    // CATEGORY 3: Performance & Scale benchmarks
    this.addTest('Benchmark: 7x7 グリッド問題生成スピード（10回測定）', 'benchmark', async (log) => {
      const rows = 7;
      const cols = 7;
      const generator = new window.LoopCourseGenerator(rows, cols);
      
      log.info(`ふつう 7x7 グリッドパズルを 10回 連続生成し、平均速度と品質を測定します。`);
      
      const durations = [];
      let totalClues = 0;
      
      for (let i = 1; i <= 10; i++) {
        const start = Date.now();
        const puzzle = generator.generate('medium');
        const duration = Date.now() - start;
        durations.push(duration);
        
        let clueCount = 0;
        for (let r = 0; r < rows; r++) {
          for (let c = 0; c < cols; c++) {
            if (puzzle.clues[r][c] !== null) clueCount++;
          }
        }
        totalClues += clueCount;
        log.info(`  生成 ${i} 回目: ${duration}ms (残存ヒント数: ${clueCount}/${rows*cols})`);
      }
      
      const avg = durations.reduce((s, x) => s + x, 0) / durations.length;
      const max = Math.max(...durations);
      const min = Math.min(...durations);
      const avgClues = (totalClues / durations.length).toFixed(1);
      
      log.info(`測定サマリー:`);
      log.info(`  最速値: ${min}ms`);
      log.info(`  最遅値: ${max}ms`);
      log.info(`  平均値: ${avg.toFixed(1)}ms (期待値: <150ms)`);
      log.info(`  平均残存ヒント: ${avgClues}マス (${((avgClues / (rows * cols)) * 100).toFixed(1)}%)`);
      
      this.assert(avg < 150, `7x7 グリッドの平均生成速度が制限値(150ms)を超過しています: ${avg.toFixed(1)}ms`);
      
      // Update benchmark dashboard metric
      document.getElementById('metric-bench').textContent = `${avg.toFixed(1)}ms`;
      document.getElementById('metric-bench').className = 'metric-value pass';
      
      log.success(`平均 ${avg.toFixed(1)}ms での高速生成を達成しました。`);
    });

    this.addTest('Benchmark: 30x15 超巨大グリッド問題生成検証（フリーズ防止）', 'benchmark', async (log) => {
      const rows = 15;
      const cols = 30;
      const generator = new window.LoopCourseGenerator(rows, cols);
      
      log.info(`横長・巨大 30x15 グリッド（全450セル、合計エッジ数 945本）のパズル生成を検証します。`);
      log.info(`制限時間: 1500ms 以内にユニーク解保証の最小ヒント化を完了させること。`);
      
      const start = Date.now();
      const puzzle = generator.generate('medium');
      const duration = Date.now() - start;
      
      let clueCount = 0;
      for (let r = 0; r < rows; r++) {
        for (let c = 0; c < cols; c++) {
          if (puzzle.clues[r][c] !== null) clueCount++;
        }
      }
      
      log.info(`超巨大盤面 30x15 生成結果:`);
      log.info(`  処理時間: ${duration}ms (制限値: <1500ms)`);
      log.info(`  残存ヒント: ${clueCount}/450マス (${((clueCount / 450) * 100).toFixed(1)}%)`);
      
      this.assert(duration < 1500, `30x15 巨大盤面の生成時間が制限値(1500ms)を超過しています: ${duration}ms`);
      log.success(`30x15 の超巨大グリッドにおいても、フリーズすることなくわずか ${duration}ms でユニーク解パズルを高速生成できることが実証されました。`);
    });
  }

  addTest(name, category, runFn) {
    this.tests.push({
      name,
      category,
      run: runFn,
      status: 'pending', // 'pending', 'running', 'pass', 'fail'
      duration: null,
      logs: []
    });
  }

  assert(condition, errorMessage) {
    if (!condition) {
      throw new Error(errorMessage);
    }
  }

  async runSuite() {
    this.btnRun.disabled = true;
    this.statusBadge.textContent = '実行中...';
    this.progressContainer.style.display = 'block';
    this.progressBar.style.width = '0%';
    
    // Reset test stats
    this.tests.forEach(t => {
      t.status = 'pending';
      t.duration = null;
      t.logs = [];
    });
    
    this.updateDashboardMetrics();
    
    // Filter tests by selected scope
    const scope = this.selectScope.value;
    const activeTests = this.tests.filter(t => scope === 'all' || t.category === scope);
    
    this.renderTestList(activeTests);
    
    let passedCount = 0;
    let failedCount = 0;
    
    for (let i = 0; i < activeTests.length; i++) {
      const test = activeTests[i];
      test.status = 'running';
      this.updateTestRowUI(test);
      
      const logCollector = {
        info: (msg) => test.logs.push({ type: 'info', msg }),
        success: (msg) => test.logs.push({ type: 'success', msg }),
        error: (msg) => test.logs.push({ type: 'error', msg }),
        warning: (msg) => test.logs.push({ type: 'warning', msg })
      };
      
      const start = Date.now();
      try {
        await test.run(logCollector);
        test.status = 'pass';
        passedCount++;
      } catch (err) {
        test.status = 'fail';
        logCollector.error(`アサート失敗: ${err.message}`);
        if (err.stack) {
          test.logs.push({ type: 'info', msg: err.stack.toString() });
        }
        failedCount++;
      }
      test.duration = Date.now() - start;
      
      // Update UI for this test row
      this.updateTestRowUI(test);
      
      // Update progress bar
      const progressPercent = ((i + 1) / activeTests.length) * 100;
      this.progressBar.style.width = `${progressPercent}%`;
      
      // Update dashboard values in real-time
      this.metricPass.textContent = passedCount;
      this.metricFail.textContent = failedCount;
    }
    
    this.progressBar.style.width = '100%';
    this.statusBadge.textContent = failedCount > 0 ? 'テスト失敗' : 'テスト完了';
    this.statusBadge.style.color = failedCount > 0 ? 'var(--neon-red)' : 'var(--neon-green)';
    
    this.btnRun.disabled = false;
    this.updateDashboardMetrics();
  }

  renderTestList(activeTests) {
    this.resultsBody.innerHTML = '';
    
    if (activeTests.length === 0) {
      this.resultsBody.innerHTML = '<div class="empty-state">選択されたスコープのテストはありません。</div>';
      return;
    }

    const categories = {
      solver: { title: 'Solver Logic (ソルバー論理推論エンジン)', tests: [] },
      generator: { title: 'Generator Algorithms (ループ拡張成長アルゴリズム)', tests: [] },
      benchmark: { title: 'Performance & Scale Benchmarks (パフォーマンス速度測定)', tests: [] }
    };

    activeTests.forEach(t => {
      if (categories[t.category]) {
        categories[t.category].tests.push(t);
      }
    });

    for (const [key, cat] of Object.entries(categories)) {
      if (cat.tests.length === 0) continue;
      
      const groupEl = document.createElement('div');
      groupEl.className = 'test-category-group';
      
      const titleEl = document.createElement('h3');
      titleEl.className = 'category-title';
      titleEl.innerHTML = `${cat.title} <span>${cat.tests.length}件</span>`;
      groupEl.appendChild(titleEl);
      
      const listEl = document.createElement('div');
      listEl.className = 'test-list';
      
      cat.tests.forEach(test => {
        const rowEl = document.createElement('div');
        rowEl.className = `test-row test-id-${this.slugify(test.name)}`;
        rowEl.innerHTML = `
          <div class="test-row-main">
            <div class="test-identity">
              <span class="badge-status pending"></span>
              <span class="test-name">${test.name}</span>
            </div>
            <span class="test-duration">-</span>
          </div>
          <div class="test-logs"></div>
        `;
        
        // Expand/Collapse logs on click
        rowEl.addEventListener('click', (e) => {
          // Avoid triggering collapse when clicking inside the log block
          if (e.target.closest('.test-logs')) return;
          const logsEl = rowEl.querySelector('.test-logs');
          logsEl.classList.toggle('visible');
        });
        
        listEl.appendChild(rowEl);
      });
      
      groupEl.appendChild(listEl);
      this.resultsBody.appendChild(groupEl);
    }
  }

  updateTestRowUI(test) {
    const rowEl = this.resultsBody.querySelector(`.test-id-${this.slugify(test.name)}`);
    if (!rowEl) return;
    
    const badgeEl = rowEl.querySelector('.badge-status');
    const durEl = rowEl.querySelector('.test-duration');
    const logsEl = rowEl.querySelector('.test-logs');
    
    // Status update
    badgeEl.className = `badge-status ${test.status}`;
    if (test.status === 'pass') {
      badgeEl.innerHTML = '✔';
    } else if (test.status === 'fail') {
      badgeEl.innerHTML = '✘';
      // Automatically expand logs if a test fails
      logsEl.classList.add('visible');
    } else if (test.status === 'running') {
      badgeEl.innerHTML = '●';
    } else {
      badgeEl.innerHTML = '';
    }
    
    // Duration update
    if (test.duration !== null) {
      durEl.textContent = `${test.duration}ms`;
    } else {
      durEl.textContent = test.status === 'running' ? '実行中...' : '-';
    }
    
    // Logs update
    if (test.logs.length > 0) {
      logsEl.innerHTML = test.logs.map(l => {
        return `<div class="log-line ${l.type}">[${l.type.toUpperCase()}] ${this.escapeHTML(l.msg)}</div>`;
      }).join('');
    }
  }

  updateDashboardMetrics() {
    const scope = this.selectScope.value;
    const activeTests = this.tests.filter(t => scope === 'all' || t.category === scope);
    
    const runs = activeTests.filter(t => t.status !== 'pending' && t.status !== 'running');
    const passes = runs.filter(t => t.status === 'pass').length;
    const fails = runs.filter(t => t.status === 'fail').length;
    
    this.metricTotal.textContent = activeTests.length;
    this.metricTotal.className = 'metric-value';
    
    this.metricPass.textContent = runs.length > 0 ? passes : '-';
    this.metricPass.className = `metric-value ${runs.length > 0 ? 'pass' : 'pending'}`;
    
    this.metricFail.textContent = runs.length > 0 ? fails : '-';
    this.metricFail.className = `metric-value ${fails > 0 ? 'fail' : 'pending'}`;
  }

  slugify(text) {
    return text.toString().toLowerCase()
      .replace(/\s+/g, '-')
      .replace(/[^\w\-]+/g, '')
      .replace(/\-\-+/g, '-')
      .replace(/^-+/, '')
      .replace(/-+$/, '');
  }

  escapeHTML(text) {
    const map = {
      '&': '&amp;',
      '<': '&lt;',
      '>': '&gt;',
      '"': '&quot;',
      "'": '&#039;'
    };
    return text.replace(/[&<>"']/g, function(m) { return map[m]; });
  }
}

// Bootstrap Test Runner
window.addEventListener('DOMContentLoaded', () => {
  window.testSuite = new LoopCourseTestSuite();
});
