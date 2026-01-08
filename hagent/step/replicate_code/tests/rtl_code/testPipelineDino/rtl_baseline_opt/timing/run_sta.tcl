	read_liberty /home/sgarg3/livehd/sky130_fd_sc_hd__ff_100C_1v95.lib
	set_units -time ns -capacitance pF -voltage V -current mA -resistance kOhm -distance um
	set_operating_conditions ff_100C_1v95
	read_verilog /home/sgarg3/livehd/pass/extractor/tests/testPipelineDino/rtl_baseline_opt/synth_file/PipelinedCPU_synth.v
	link_design PipelinedCPU
	read_sdc PipelinedCPU.sdc
	report_checks -path_delay max > /home/sgarg3/livehd/pass/extractor/tests/testPipelineDino/rtl_baseline_opt/timing/timing_report.rpt
