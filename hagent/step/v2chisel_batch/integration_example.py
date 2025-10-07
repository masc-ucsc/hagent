#!/usr/bin/env python3
# Example of how to integrate PipelineReporter into v2chisel_batch.py
# This shows the minimal changes needed

from components.pipeline_reporter import PipelineReporter


def example_v2chisel_batch_integration():
    """
    Example showing how to integrate PipelineReporter into v2chisel_batch
    with minimal code changes
    """

    # 1. Initialize reporter at the beginning of v2chisel_batch
    reporter = PipelineReporter()

    # Example processing multiple bugs
    bugs = ['NextPC.sv', 'ALU.sv', 'Control.sv']

    for i, bug_file in enumerate(bugs, 1):
        print(f'\n🔄 Processing Bug #{i}: {bug_file}')

        # 2. Create report for this bug
        report = reporter.create_report(bug_file)

        # Simulate retry loop (max 3 iterations)
        for iteration in range(1, 4):
            print(f'   ⏳ Iteration {iteration}')

            # 3. Add iteration tracking
            report.add_iteration(iteration)

            # Simulate LLM call
            print('   🤖 [LLM] Generating Chisel diff...')
            llm_success = True  # Simulate success
            if llm_success:
                # 4. Mark LLM success
                report.mark_llm_success()
                print('   ✅ LLM generated diff successfully')
            else:
                continue

            # Simulate compilation
            print('   🏗️  [COMPILE] Compiling Chisel...')
            compile_success = (iteration == 2 and bug_file == 'NextPC.sv') or (iteration == 1 and bug_file != 'ALU.sv')

            if compile_success:
                # 5. Mark compilation success
                report.mark_compilation_success()
                print('   ✅ Compilation successful')
            else:
                print('   ❌ Compilation failed')
                continue

            # Simulate Verilog generation
            print('   🔧 [VERILOG] Generating Verilog...')
            verilog_success = True  # Always succeeds if compilation succeeded
            if verilog_success:
                # 6. Mark Verilog success
                report.mark_verilog_success()
                print('   ✅ Verilog generation successful')
            else:
                continue

            # Simulate LEC
            print('   🔍 [LEC] Running equivalence check...')
            lec_success = bug_file == 'NextPC.sv'  # Only NextPC succeeds

            if lec_success:
                # 7. Mark LEC success
                report.mark_lec_success()
                print('   🎉 LEC successful!')
                break  # Success, exit retry loop
            else:
                print('   ❌ LEC failed')

            # If this was the last iteration, break
            if iteration == 3:
                break

    # 8. Print final summary at the end
    print('\n' + '=' * 80)
    print('🎯 FINAL RESULTS')
    print('=' * 80)
    reporter.print_all_summaries()


if __name__ == '__main__':
    example_v2chisel_batch_integration()
