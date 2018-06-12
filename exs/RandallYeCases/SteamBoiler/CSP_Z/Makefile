NOW := $(shell date +"%Y%m%d%H%M%S" | tr ' :' '__')

zfile = SteamBoiler_z.fuzz
cspfile = SteamBoiler_csp.csp
PROB_OPTS = $(zfile) 
PROB_OPTS += -csp-guide $(cspfile) -MAIN MAIN
#PROB_OPTS += -prefs ~/ProB_Preferences.pl 
#PROB_OPTS += -p MAXINT 24 
PROB_OPTS += -p TIME_OUT 500000
PROB_OPTS += -p COMPRESSION TRUE  
#PROB_OPTS += -p FORGET_STATE_SPACE TRUE  
#PROB_OPTS += -p IGNORE_HASH_COLLISIONS TRUE  
PROB_OPTS += -v 
#PROB_OPTS += -df 
PROB_OPTS += -mc_mode mixed  
PROB_OPTS += -strict 
PROB_OPTS += -init
#PROB_OPTS += -his history -his_option 0

# model_check
#MC_PROB_OPTS = $(PROB_OPTS) -mc 1000000 
MC_PROB_OPTS = $(PROB_OPTS) -model_check
MC_PROB_OPTS += -l modelcheck_$(NOW).log
MC_PROB_OPTS += >modelcheck_$(NOW).out 2>&1 & 

# animation
ANI_PROB_OPTS = $(PROB_OPTS)
ANI_PROB_OPTS += -animate_all 
#ANI_PROB_OPTS += -animate_stats
ANI_PROB_OPTS += -l animation_$(NOW).log
ANI_PROB_OPTS += >animation_$(NOW).out 2>&1 &

# deadlock failures
DEADF_PROB_OPTS = $(PROB_OPTS)
DEADF_PROB_OPTS += -cspdeadlock MAIN F 
DEADF_PROB_OPTS += -l deadlock_f_$(NOW).log
DEADF_PROB_OPTS += >deadlock_f_$(NOW).out 2>&1 & 

# deadlock failures-divergences.
DEADFD_PROB_OPTS = $(PROB_OPTS)
DEADFD_PROB_OPTS += -cspdeadlock MAIN FD #$(cspfile)
DEADFD_PROB_OPTS += -l deadlock_fd_$(NOW).log
DEADFD_PROB_OPTS += >deadlock_fd_$(NOW).out 2>&1 &

# livelock 
LIVELOCK_PROB_OPTS = $(PROB_OPTS)
LIVELOCK_PROB_OPTS += -csplivelock MAIN #$(cspfile)
LIVELOCK_PROB_OPTS += -l livelock_$(NOW).log
LIVELOCK_PROB_OPTS += -cache cache_livelock
LIVELOCK_PROB_OPTS += >livelock_$(NOW).out 2>&1 &

# cbc_deadlock
CBCDEAD_PROB_OPTS = $(PROB_OPTS)
CBCDEAD_PROB_OPTS += -cbc_deadlock
CBCDEAD_PROB_OPTS += -l cbc_deadlock_$(NOW).log
#CBCDEAD_PROB_OPTS += -cache cache_livelock
CBCDEAD_PROB_OPTS += >cbc_deadlock_$(NOW).out 2>&1 & 

# bmc 
BMC_PROB_OPTS = $(PROB_OPTS)
BMC_PROB_OPTS += -bmc 20
BMC_PROB_OPTS += -l bmc_deadlock_$(NOW).log
BMC_PROB_OPTS += -cache cache_livelock
BMC_PROB_OPTS += >bmc_deadlock_$(NOW).out 2>&1 &

# ltl
LTLF_PROB_OPTS = $(PROB_OPTS)
LTLF_PROB_OPTS += -df 
LTLF_PROB_OPTS += -ltlfile formulas.ltl
LTLF_PROB_OPTS += -ltllimit 1000000
LTLF_PROB_OPTS += -l ltlfile_$(NOW).log
LTLF_PROB_OPTS += -cache cache_livelock
LTLF_PROB_OPTS += >ltlfile_$(NOW).out 2>&1 &

.PHONY: model_check animation deadlock_f deadlock_fd livelock cbc_deadlock bmc ltlfile prob

model_check: 
	@echo "probcli.sh $(MC_PROB_OPTS)"
	@probcli.sh $(MC_PROB_OPTS)

animation:
	@echo "probcli.sh $(ANI_PROB_OPTS)"
	@probcli.sh $(ANI_PROB_OPTS)

deadlock_f:
	@echo "probcli.sh $(DEADF_PROB_OPTS)"
	@probcli.sh $(DEADF_PROB_OPTS)

deadlock_fd:
	@echo "probcli.sh $(DEADFD_PROB_OPTS)"
	@probcli.sh $(DEADFD_PROB_OPTS)

livelock:
	@echo "probcli.sh $(LIVELOCK_PROB_OPTS)"
	@probcli.sh $(LIVELOCK_PROB_OPTS)

cbc_deadlock:
	@echo "probcli.sh $(CBCDEAD_PROB_OPTS)"
	@probcli.sh $(CBCDEAD_PROB_OPTS)

bmc:
	@echo "probcli.sh $(BMC_PROB_OPTS)"
	@probcli.sh $(BMC_PROB_OPTS)

ltlfile:
	@echo "probcli.sh $(LTLF_PROB_OPTS)"
	@probcli.sh $(LTLF_PROB_OPTS)

prob:
	@StartProB.sh > probgui-$(NOW).log 2>&1 &
