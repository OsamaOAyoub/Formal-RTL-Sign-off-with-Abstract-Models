#------------------------------------------------------------------
# Setup mode
#------------------------------------------------------------------
set_mode setup
delete_design -both
#------------------
# Set path variable
#------------------
  #cd ""  
  set SCRIPT_LOCATION [file dirname [file normalize [info script]]]
  
  set RTL_PATH $SCRIPT_LOCATION/rtl
  set PROP_PATH $SCRIPT_LOCATION/sva

#----------------------
# Read Library files:
#----------------------

#----------------------
# Read RTL files:
#----------------------

read_verilog -golden  -pragma_ignore {}  -version sv2012 {$SCRIPT_LOCATION/VerificationWrapper.sv}

elaborate -golden
compile -golden
#------------------------------------------------------------------
# MV mode
#------------------------------------------------------------------

set_mode mv
set_check_option -verbose
#----------------------
# Read SVA files:
#----------------------

#read_sva -version sv2012 {$SCRIPT_LOCATION/cntr_sva.sv}

#--------------------------------
# check properties
#--------------------------------

time {check -all [get_checks]}
