const createLoopCourseModule = require('./js/loopcourse.js');

async function measureAlgorithms() {
    console.log("Loading WebAssembly module...");
    const Module = await createLoopCourseModule();
    
    const init_grid = Module.cwrap('init_grid', null, ['number', 'number']);
    const set_random_seed = Module.cwrap('set_random_seed', null, ['number']);
    const generate_puzzle_wasm = Module.cwrap('generate_puzzle_wasm', null, ['string']);
    
    const reset_perf = Module.cwrap('reset_perf', null, []);
    const get_perf_static = Module.cwrap('get_perf_static', 'number', []);
    const get_perf_lut = Module.cwrap('get_perf_lut', 'number', []);
    const get_perf_ac3 = Module.cwrap('get_perf_ac3', 'number', []);
    const get_perf_gf2 = Module.cwrap('get_perf_gf2', 'number', []);
    const get_perf_lookahead = Module.cwrap('get_perf_lookahead', 'number', []);

    // AC3 Sub-profiling
    const get_ac3_rule_name = Module.cwrap('get_ac3_rule_name', 'string', ['number']);
    const get_ac3_rule_time = Module.cwrap('get_ac3_rule_time', 'number', ['number']);
    const get_ac3_rule_hit_count = Module.cwrap('get_ac3_rule_hit_count', 'number', ['number']);
    const get_ac3_rule_count = Module.cwrap('get_ac3_rule_count', 'number', []);
    const reset_ac3_rule_times = Module.cwrap('reset_ac3_rule_times', null, []);

    // Parse command line arguments or use defaults
    const args = process.argv.slice(2);
    const difficulty = args[0] || "Master";
    const rows = parseInt(args[1]) || 20;
    const cols = parseInt(args[2]) || 20;

    console.log(`\n--- Measuring Algorithms on [${rows}x${cols} ${difficulty}] Puzzle ---`);
    init_grid(rows, cols);
    reset_perf();
    reset_ac3_rule_times();
    
    set_random_seed(Date.now() % 1000000);
    
    let t0 = performance.now();
    generate_puzzle_wasm(difficulty);
    let t1 = performance.now();
    
    let time_total = t1 - t0;
    let time_static = get_perf_static();
    let time_lut = get_perf_lut();
    let time_ac3 = get_perf_ac3();
    let time_gf2 = get_perf_gf2();
    let time_lookahead = get_perf_lookahead();
    
    console.log(`Puzzle generation finished in: ${time_total.toFixed(2)} ms\n`);
    console.log(`[Algorithm Time Breakdown]`);
    console.log(`- 1. 定石ロジック (Static Rules)      : ${(time_static - time_lut).toFixed(2)} ms`);
    console.log(`- 2. パターン辞書 (LUT/Boundary LUT)  : ${time_lut.toFixed(2)} ms`);
    console.log(`- 3. AC-3 (制約伝播)                  : ${time_ac3.toFixed(2)} ms`);
    console.log(`- 4. パリティ推論 (GF2)               : ${time_gf2.toFixed(2)} ms`);
    console.log(`- 5. 先読み推論 (Lookahead)           : ${time_lookahead.toFixed(2)} ms`);
    
    let other_time = time_total - (time_static + time_ac3 + time_gf2 + time_lookahead);
    console.log(`- その他 (生成ロジック, バックトラック等) : ${other_time.toFixed(2)} ms\n`);

    console.log(`[AC-3 Internal Time Breakdown]`);
    let ac3_count = get_ac3_rule_count();
    let ac3_sum = 0;
    for (let i = 0; i < ac3_count; i++) {
        let name = get_ac3_rule_name(i);
        let t = get_ac3_rule_time(i);
        let hits = get_ac3_rule_hit_count(i);
        ac3_sum += t;
        console.log(`  - ${name.padEnd(30, ' ')}: ${t.toFixed(2)} ms | Hits: ${hits}`);
    }
    console.log(`  - (Internal queue handling overhead)    : ${(time_ac3 - ac3_sum).toFixed(2)} ms`);
    
    // --- Export Deduction Logs to CSV ---
    console.log(`\n[Analyzer] Running deduction trace for the final generated puzzle...`);
    const analyze_puzzle = Module.cwrap('analyze_puzzle', null, ['string']);
    const get_deduction_log_count = Module.cwrap('get_deduction_log_count', 'number', []);
    const get_deduction_logs_ptr = Module.cwrap('get_deduction_logs_ptr', 'number', []);
    
    analyze_puzzle(difficulty);
    let logCount = get_deduction_log_count();
    let logsPtr = get_deduction_logs_ptr();
    
    // DeductionLog is { int edgeIdx; int ruleId; int depth; } (12 bytes per struct)
    // 32-bit wasm, so int is 4 bytes.
    let HEAP32 = new Int32Array(Module.HEAP8.buffer);
    let csvData = "Step,EdgeIdx,RuleID,Difficulty,RuleName,LookaheadDepth\n";
    for(let i=0; i<logCount; i++) {
        let edgeIdx = HEAP32[(logsPtr >> 2) + i * 3 + 0];
        let ruleId  = HEAP32[(logsPtr >> 2) + i * 3 + 1];
        let depth   = HEAP32[(logsPtr >> 2) + i * 3 + 2];
        let rname = get_ac3_rule_name(ruleId);
        
        let diff = 0;
        if (ruleId >= 101 && ruleId <= 109) diff = 1;
        else if (ruleId >= 111 && ruleId <= 119) diff = 2;
        else if (ruleId >= 121 && ruleId <= 129) diff = 3;
        else if (ruleId >= 131 && ruleId <= 139) diff = 4;
        else if (ruleId >= 141 && ruleId <= 149) diff = 6;
        else if (ruleId >= 151 && ruleId <= 159) diff = 8;
        else if (ruleId == 200 || depth > 0) diff = 10 + depth;
        else diff = ruleId; // fallback
        
        csvData += `${i+1},${edgeIdx},${ruleId},${diff},"${rname}",${depth}\n`;
    }
    
    const fs = require('fs');
    fs.writeFileSync('deduction_log.csv', csvData);
    console.log(`[Analyzer] Successfully dumped ${logCount} deduction steps to 'deduction_log.csv'.`);
}

measureAlgorithms();
