### Tesina Ricerca Operativa 
### Andrea Incerti Delmonte 239629


### SETS 

set INTERNAL_SENIOR_STAFF;
set INTERNAL_JUNIOR_STAFF;
set CONSULTANTS;
  
set TASKS;
set INTERNAL_STAFF_TASKS;
set SENIOR_AND_CONSULTANTS_TASKS;   


### PARAMETERS 

param sprint_length > 0;
param max_internal_hpc_hours_per_senior > 0;
param min_internal_hours_per_junior > 0;

param iss_efficiency{INTERNAL_SENIOR_STAFF} > 0;
param ijs_efficiency{INTERNAL_JUNIOR_STAFF} > 0;
param c_efficiency{CONSULTANTS} > 0;
 
param iss_hourly_cost{INTERNAL_SENIOR_STAFF} > 0;
param ijs_hourly_cost{INTERNAL_JUNIOR_STAFF} > 0;
param c_hourly_cost{CONSULTANTS} > 0; 

param task_effort{TASKS} > 0;
param is_task_effort{INTERNAL_STAFF_TASKS} > 0;
param sc_task_effort{SENIOR_AND_CONSULTANTS_TASKS} > 0;

param is_task_coupling{INTERNAL_STAFF_TASKS,INTERNAL_STAFF_TASKS}>=0;


# Check that task doesn't exceed team work capacity
check : sum{t in TASKS} task_effort[t] + 
		sum{ist in INTERNAL_STAFF_TASKS} is_task_effort[ist] +
		sum{sct in SENIOR_AND_CONSULTANTS_TASKS} sc_task_effort[sct] <= 
		sum{iss in INTERNAL_SENIOR_STAFF} iss_efficiency[iss]*sprint_length +
		sum{ijs in INTERNAL_JUNIOR_STAFF} ijs_efficiency[ijs]*sprint_length +  
		sum{c in CONSULTANTS} c_efficiency[c]*sprint_length;   
		
# Check that s&c task doesn't exceed senior and consultant work capacity
# Applied hpc limit
check : sum{sct in SENIOR_AND_CONSULTANTS_TASKS} sc_task_effort[sct] <= 
		sum{iss in INTERNAL_SENIOR_STAFF} iss_efficiency[iss]*	 +		
		sum{c in CONSULTANTS} c_efficiency[c]*sprint_length;		

# Checks on internal task coupling
# Check for tasks coupled with themselves
check {ist in INTERNAL_STAFF_TASKS}:
	is_task_coupling[ist,ist] == 0;

# Check bidirectional coupling a with b and b with a
check {ist1 in INTERNAL_STAFF_TASKS,ist2 in INTERNAL_STAFF_TASKS}:
	is_task_coupling[ist1,ist2] = is_task_coupling[ist2,ist1];  

# Check that row sum is less and equal to 1
check {ist1 in INTERNAL_STAFF_TASKS}:
	sum {ist2 in INTERNAL_STAFF_TASKS} is_task_coupling[ist1,ist2] <= 1;
		
### VARIABLES 

# Task assignments
var iss_t_assignments{INTERNAL_SENIOR_STAFF, TASKS} binary;
var ijs_t_assignments{INTERNAL_JUNIOR_STAFF, TASKS} binary;
var c_t_assignments{CONSULTANTS, TASKS} binary; 

# Internal task assignments
var iss_ist_assignments{INTERNAL_SENIOR_STAFF, INTERNAL_STAFF_TASKS} binary;
var ijs_ist_assignments{INTERNAL_JUNIOR_STAFF, INTERNAL_STAFF_TASKS} binary;

# Senior and consultants task assignments
var iss_sct_assignments{INTERNAL_SENIOR_STAFF, SENIOR_AND_CONSULTANTS_TASKS} binary;
var c_sct_assignments{CONSULTANTS, SENIOR_AND_CONSULTANTS_TASKS} binary;


### CONSTRAINTS  

# Each task can be assigned to only one developer

# Task
subject to one_dev_per_task {t in TASKS}: 
	sum{iss in INTERNAL_SENIOR_STAFF} iss_t_assignments[iss,t] +
	sum{ijs in INTERNAL_JUNIOR_STAFF} ijs_t_assignments[ijs,t] +  
	sum{c in CONSULTANTS} c_t_assignments[c,t]= 1;
	
# Internal task
subject to one_dev_per_is_task {ist in INTERNAL_STAFF_TASKS}: 
	sum{iss in INTERNAL_SENIOR_STAFF} iss_ist_assignments[iss,ist] +
	sum{ijs in INTERNAL_JUNIOR_STAFF} ijs_ist_assignments[ijs,ist] = 1;

# Senior and consultant task
subject to one_dev_per_scs_task {sct in SENIOR_AND_CONSULTANTS_TASKS}: 
	sum{iss in INTERNAL_SENIOR_STAFF} iss_sct_assignments[iss,sct] +
	sum{c in CONSULTANTS} c_sct_assignments[c,sct]= 1;

# Work assigned to each dev doesn't exceed his capacity

# Senior internal dev
subject to iss_single_dev_capacity {iss in INTERNAL_SENIOR_STAFF}: 
	sum{t in TASKS} iss_t_assignments[iss,t]*task_effort[t]/iss_efficiency[iss] + 
	sum{ist in INTERNAL_STAFF_TASKS} iss_ist_assignments[iss,ist]*is_task_effort[ist]/iss_efficiency[iss] +
	sum{sct in SENIOR_AND_CONSULTANTS_TASKS} iss_sct_assignments[iss,sct]*sc_task_effort[sct]/iss_efficiency[iss] 
	<= sprint_length;

# Junior internal dev
subject to ijs_single_dev_capacity {ijs in INTERNAL_JUNIOR_STAFF}: 
	sum{t in TASKS} ijs_t_assignments[ijs,t]*task_effort[t]/ijs_efficiency[ijs] + 
	sum{ist in INTERNAL_STAFF_TASKS} ijs_ist_assignments[ijs,ist]*is_task_effort[ist]/ijs_efficiency[ijs] 
	<= sprint_length;

# Consultant dev
subject to c_dev_single_capacity {c in CONSULTANTS}: 
	sum{t in TASKS} c_t_assignments[c,t]*task_effort[t]/c_efficiency[c] +
	sum{sct in SENIOR_AND_CONSULTANTS_TASKS} c_sct_assignments[c,sct]*sc_task_effort[sct]/c_efficiency[c]
	<= sprint_length;

# Total s&c task hours assigned to senior must non exceed max_internal_hpc_hours_per_senior 
subject to max_internal_hpc_capacity {iss in INTERNAL_SENIOR_STAFF}:
	sum{sct in SENIOR_AND_CONSULTANTS_TASKS} iss_sct_assignments[iss,sct]*sc_task_effort[sct]/iss_efficiency[iss] <= max_internal_hpc_hours_per_senior; 

# Min number of internal task hours to be assigned to junior
subject to min_internal_junior_assignments {ijs in INTERNAL_JUNIOR_STAFF}:
	sum{ist in INTERNAL_STAFF_TASKS} ijs_ist_assignments[ijs,ist]*is_task_effort[ist]/ijs_efficiency[ijs] >= min_internal_hours_per_junior; 

# Internal senior staff task coupling
subject to is_task_performed_in_pair_from_senior {iss in INTERNAL_SENIOR_STAFF, ist1 in INTERNAL_STAFF_TASKS, ist2 in INTERNAL_STAFF_TASKS}:
	iss_ist_assignments[iss,ist1]*is_task_coupling[ist1,ist2] = iss_ist_assignments[iss,ist2]*is_task_coupling[ist2,ist1];

# Internal junior staff task coupling 
subject to is_task_performed_in_pair_from_junior {ijs in INTERNAL_JUNIOR_STAFF, ist1 in INTERNAL_STAFF_TASKS, ist2 in INTERNAL_STAFF_TASKS}:
	ijs_ist_assignments[ijs,ist1]*is_task_coupling[ist1,ist2] = ijs_ist_assignments[ijs,ist2]*is_task_coupling[ist2,ist1];

### OBJECTIVE 

minimize sprint_cost: 
	sum{iss in INTERNAL_SENIOR_STAFF, t in TASKS} iss_hourly_cost[iss]*iss_t_assignments[iss,t]*task_effort[t]/iss_efficiency[iss] +
	sum{ijs in INTERNAL_JUNIOR_STAFF, t in TASKS} ijs_hourly_cost[ijs]*ijs_t_assignments[ijs,t]*task_effort[t]/ijs_efficiency[ijs] + 
	sum{c in CONSULTANTS, t in TASKS} c_hourly_cost[c]*c_t_assignments[c,t]*task_effort[t]/c_efficiency[c] + 
	sum{iss in INTERNAL_SENIOR_STAFF, ist in INTERNAL_STAFF_TASKS} iss_hourly_cost[iss]*iss_ist_assignments[iss,ist]*is_task_effort[ist]/iss_efficiency[iss] +
	sum{ijs in INTERNAL_JUNIOR_STAFF, ist in INTERNAL_STAFF_TASKS} ijs_hourly_cost[ijs]*ijs_ist_assignments[ijs,ist]*is_task_effort[ist]/ijs_efficiency[ijs] +
	sum{iss in INTERNAL_SENIOR_STAFF, sct in SENIOR_AND_CONSULTANTS_TASKS} iss_hourly_cost[iss]*iss_sct_assignments[iss,sct]*sc_task_effort[sct]/iss_efficiency[iss] +
	sum{c in CONSULTANTS, sct in SENIOR_AND_CONSULTANTS_TASKS} c_hourly_cost[c]*c_sct_assignments[c,sct]*sc_task_effort[sct]/c_efficiency[c];






