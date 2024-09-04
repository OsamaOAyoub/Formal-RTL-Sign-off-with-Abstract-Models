####################################################
# Copyright(c) LUBIS EDA GmbH, All rights reserved #
# Contact: contact@lubis-eda.com                   #
####################################################
#--------------------------------------------------------------------
# Setup mode
#--------------------------------------------------------------------
set_mode setup
delete_design -both
#------------------
# Set path variable
#------------------
set SCRIPT_LOCATION [file dirname [file normalize [info script]]]

#------------------
# Read RTL files:
#------------------
read_verilog -golden  -pragma_ignore {}  -version sv2012 {$SCRIPT_LOCATION/VerificationWrapper.sv}

set_elaborate_option -golden -call_threshold 100 -loop_iter_threshold 300 -x_optimism -verilog_parameter {} -verilog_library_search_order {} -no_verilog_library_resolution_ieee_compliance -no_verilog_config_support -vhdl_generic {} -vhdl_assertion_report_prefix {onespin} -black_box {} -black_box_empty_modules -no_black_box_missing_modules -black_box_library {} -black_box_component {} -top {Verilog!work.VerificationWrapper}
elaborate -golden
compile -golden
#--------------------------------------------------------------------
# MV mode
#--------------------------------------------------------------------
set_mode mv
set_check_option -verbose
#time {check -all [get_checks]}
