param number_of_nurses := 7;
param number_of_days := 14;
param number_of_shifts := 3;

param points_pc := 1;
param points_upc := 1;
param points_ps := 1;
param points_ups := 1;


param max_night_shifts :=6;

set nurses := {1..number_of_nurses}; #pielêgniarki
set shifts := {1..number_of_shifts}; #zmiany
set days := {1..number_of_days}; #dni
set all_shifts := {1..number_of_days * number_of_shifts}; #dni
# zmiany * dni

param demand {days, shifts} >= 0, integer;    #zapotrzebowanie danego dnia i zmiany na pielêgniarki
param workhours {nurses} > 0, integer;             #limit pracy pielêgniarki
param vacation {nurses, days}, binary;
param preferred_companions {nurses, nurses}, binary; 
param unpreferred_companions {nurses, nurses}, binary; 
param preferred_shifts {nurses, days, shifts}, binary; 
param unpreferred_shifts {nurses, days, shifts}, binary; 
param last_shift {nurses}, binary; 


	 	 
var schedule {nurses, days, shifts}, binary; #grafik

var all_shifts_matrix {nurses, all_shifts}, binary; #grafik

var interactions{nurses, nurses, days, shifts},binary; # interakcje dla preferred_companions

var if_working{nurses, {1..(number_of_days  - 1) * number_of_shifts + 1}},binary; # macierz dla 08 weekend
 

	 
	 
maximize points:
	
	#companions
	points_pc * sum{i in nurses, j in nurses,d in days, s in shifts}
	((interactions[i,j,d,s]*preferred_companions[i,j]))-
	
	points_upc * sum{i in nurses, j in nurses, d in days, s in shifts}
	((interactions[i,j,d,s]*unpreferred_companions[i,j]))+

	#shifts
	points_ps * sum{n in nurses, d in days, s in shifts}
	(schedule[n,d,s] * preferred_shifts[n,d,s])-
	
	points_ups * sum{n in nurses, d in days, s in shifts}
	(schedule[n,d,s] * unpreferred_shifts[n,d,s]);
	
	

#00 interakcje (¿eby by³o liniowo)
subject to interactions_max {i in nurses, j in nurses, d in days, s in shifts}:
	 interactions[i,j,d,s] <= 0.5*(schedule[i,d,s] + schedule[j,d,s]);

subject to interactions_min {i in nurses, j in nurses, d in days, s in shifts}:
	 interactions[i,j,d,s] >= (schedule[i,d,s] + schedule[j,d,s]) - 1;



#01 jeden dzieñ
subject to one_day {n in nurses, d in days}:
	sum{s in shifts} schedule[n, d, s] <= 1;
	



#02 noc =/=> nie rano
subject to not_morning {n in nurses, d in {1..(number_of_days-1)}}:
	schedule[n, d, number_of_shifts] + schedule[n, d+1, 1]   <= 1;


#03 noc poprzedniego miesiaca  =/=> nie rano (dodakowa zmienna last_shift)
subject to not_last_shift {n in nurses}:
	schedule[n, 1, 1] + last_shift[n]  <= 1;	

	
#04 pielêgniarka pracuje mniej niz < xx 
subject to working_less_than {n in nurses}:
	sum{d in days, s in shifts} schedule[n, d, s] <= workhours[n] / (24/number_of_shifts);

	
	
#05 zapotrzebowanie zmian = xx
subject to demand_satisfied {d in days, s in shifts}:
	sum{n in nurses} schedule[n, d, s] = demand[d, s];
	


#06 urlopy
subject to vacation_satisfied {n in nurses, d in days}:
	sum{s in shifts} (schedule[n, d, s] * vacation[n, d]) = 0;
	
	
#07 max nocne zmiany 
subject to night_shifts {n in nurses, k in {1..(number_of_days/7)}}: 
	sum{i in {1..7}}  schedule[n, 7 *(k-1)+i, number_of_shifts] <= max_night_shifts;



#08  24h wolne
subject to crearte_shfits {n in nurses, d in days, s in shifts}:
	 all_shifts_matrix[n, number_of_shifts * (d- 1) + s] = schedule [n, d, s]; 



#08  24h wolne
subject to if_working_max {n in nurses, s in {1..(number_of_days  - 1) * number_of_shifts + 1}}:
	 if_working[n,s] <=  sum{i in {1..number_of_shifts}} all_shifts_matrix[n, s + i - 1] ; 

subject to if_working_min {n in nurses, s in {1..(number_of_days  - 1) * number_of_shifts + 1}}:
	 if_working[n,s] >= (sum{i in {1..number_of_shifts}} all_shifts_matrix[n, s + i - 1]) / 1000; #number_of_shifts + 1 (tak ¿eby by³o mniejsze od 1) 


subject to free_day_in_week {n in nurses}:
	 sum{s in {1..(number_of_days  - 1) * number_of_shifts + 1}} if_working[n,s] <= number_of_days * number_of_shifts - number_of_shifts;



#09 ile srendnio pielegniarka musi pracowac w weekend
param weekend_avg_demand := sum{i in shifts, k in {1..(number_of_days/7)}}  (demand[7 * (k-1) + 6, i] + demand[7 * (k-1) + 7, i]) / number_of_nurses;
param bias:= 1;


# weekendy równo roz³o¿one 
subject to weekends_max {n in nurses, k in {1..(number_of_days/7)}}:
  sum{i in shifts} (schedule[n, 7 * (k-1) + 6, i] + schedule[n, 7 * (k-1) + 7, i])  <= weekend_avg_demand * (1 + bias);
  
subject to weekends_min {n in nurses, k in {1..(number_of_days/7)}}:  
  sum{i in shifts} (schedule[n, 7 * (k-1) + 6, i] + schedule[n, 7 * (k-1) + 7, i]) >= weekend_avg_demand * (1 - bias);
  
  

#pozostale rzeczy do zrobienia 
# 1) ka¿da pielêgniarka ma raz w tygodniu 24h wolne (*) #08 <-- nie dziala

