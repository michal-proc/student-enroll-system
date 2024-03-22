include "globals.mzn";

% Parameters
int: n_students;
int: n_days;
int: n_classes;
int: n_groups;
int: n_time_units_in_hour;
int: exclusion = -1;

set of int: Student = 1..n_students;
set of int: Class = 1..n_classes;
set of int: Group = 1..n_groups;
set of int: Day = 1..n_days;
set of int: Time = 0..n_time_units_in_hour * 24;
set of int: TimeNegative = -n_time_units_in_hour * 24..n_time_units_in_hour * 24;
set of int: WorkTime = 0..max(Time)*n_days;
set of int: Preference = exclusion..max([student_prefers[s,g] | s in Student, g in Group]);

array[Student] of 0..5: student_break_importance;
array[Student, Group] of int: student_prefers;

array[Class] of Time: class_duration;
array[Class] of int: class_size;

array[Group] of Class: group_class;
array[Group] of Time: group_start;
array[Group] of Day: group_day;
array[Group, Group] of bool: groups_conflicts;

% Variables
array[Student] of var set of Group: assignment;
array[Student] of var int: preference_disappointment;
array[Student, Day] of var Time: earliest_class_start;
array[Student, Day] of var Time: latest_class_end;
array[Student, Day] of var Time: total_class_duration;
array[Student, Day] of var Time: time_at_university;
array[Student, Day] of var TimeNegative: wasted_time; % It's possible, that wasted_time is negative, so we handle NegativeTime, not Time
array[Student] of var int: break_disappointment;
var int: total_preference_disappointment;
var int: total_break_disappointment;
var int: objective;

% Helpers
function var int: ceil_div(var int: x, var int: y) =
  x div y + ((x mod y) > 0);
  
function var Time: group_end(var Group: g) =
  group_start[g] + class_duration[group_class[g]];
  

% Constraints


% Need to ensure that no more than one group in each class will be assigned to each student 
constraint forall(s in Student)(
    alldifferent(g in assignment[s])
);

% Need to ensure that students won't get groups which are set as excluded for them
constraint forall(s in Student)(
    forall(g in assignment[s])(
        student_prefers[s, g] != exclusion
    )
);

% Students need to sit somewhere :)
constraint forall(g in Group)(
    sum(s in Student) (
        g in assignment[s]
    ) <= class_size[group_class[g]]
);

% Need to ensure that students won't get conflict groups
constraint forall(s in Student) (
    forall(g1, g2 in assignment[s] where g1 < g2) (
        not groups_conflicts[g1,g2]
    )
);

% Students should be assigned to all classes they should attend
constraint forall(s in Student, c in Class) (
    (exists(g in Group where group_class[g] = c) (student_prefers[s, g] != exclusion)) 
      -> 
    (exists(g in Group where group_class[g] = c) (g in assignment[s]))
);

% Calculate student day start
constraint forall(s in Student, d in Day)(
    if exists(g in Group)(g in assignment[s] /\ group_day[g] = d) then
        earliest_class_start[s, d] = min([group_start[g] | g in Group where g in assignment[s] /\ group_day[g] = d])
    else
        earliest_class_start[s, d] = max(Time)
    endif
);

% Calculate student day end
constraint forall(s in Student, d in Day)(
    if exists(g in Group)(g in assignment[s] /\ group_day[g] = d) then
        latest_class_end[s, d] = max([group_end(g) | g in Group where g in assignment[s] /\ group_day[g] = d])
    else
        latest_class_end[s, d] = max(Time)
    endif
);

% Calculate time spent at university for each student and day
constraint forall(s in Student, d in Day)(
    if exists(g in Group)(g in assignment[s] /\ group_day[g] = d) then
        time_at_university[s, d] = latest_class_end[s, d] - earliest_class_start[s, d]
    else
        time_at_university[s, d] = 0
    endif
);

% Calculate total class duration for each student and day
constraint forall(s in Student, d in Day)(
    total_class_duration[s, d] = max(0, sum(g in Group where g in assignment[s] /\ group_day[g] = d) (class_duration[group_class[g]]))
);

% Calculate break time for each student and day
constraint forall(s in Student, d in Day)(
    wasted_time[s, d] = time_at_university[s, d] - total_class_duration[s, d]
);

% Sum and normalize the wasted time for each student to full hours
constraint forall(s in Student)(
    break_disappointment[s] = ceil_div(sum(d in Day)(wasted_time[s, d]), n_time_units_in_hour)
);
 
% Calculate preference dissapointment for each student
constraint forall(s in Student) (
    preference_disappointment[s] = sum(g in assignment[s]) (max(0, max([student_prefers[s, g2] | g2 in Group where group_class[g2] = group_class[g]]) - student_prefers[s, g]))
);

total_preference_disappointment = sum(s in Student) (preference_disappointment[s]);
total_break_disappointment = sum(s in Student) (break_disappointment[s]);

objective = sum(s in Student) ((ceil_div(student_break_importance[s] * break_disappointment[s] + (10 - student_break_importance[s]) * preference_disappointment[s], 10))^2);

solve :: seq_search([int_search(preference_disappointment, first_fail, indomain_min), int_search(break_disappointment, first_fail, indomain_min)]) minimize objective;

output [
    "assignment = ", show(assignment), ";\n",
    "total_break_disappointment = ", show(total_break_disappointment), ";\n",
    "total_preference_disappointment = ", show(total_preference_disappointment), ";\n",
    "objective = ", show(objective), ";\n"
];
