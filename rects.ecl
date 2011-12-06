:- lib(fd).
:- lib(fd_search).	
:- lib(fd_global).	
:- import problems.

% solve(11,R,C, anti_first_fail, indomain_split, bbs(W + H + Max), 1,30).

% a strawberry should be covered by exactly 1 greenhouse
covered(X, Y, Rects, Max) :-	
	dim(Cover, [Max]),
	Cover[1..Max] :: 0..1,
	( for(I, 1, Max), param(X, Y, Rects, Cover) do
		((Rects[I,1] #<= X) #/\ (Rects[I,2] #<= Y) #/\ (Rects[I,3] #> X) #/\ (Rects[I,4] #> Y)) #<=> (Cover[I] #= 1)
	),
	occurrences(1, Cover, 1).

% count occurences of Ex in List, return in Count
count(List, Ex, Count) :-
	( foreach(El, List), param(Ex), fromto(0, S1, S2, Count) do
		( El = Ex -> S2 is S1 + 1 ; S2 is S1 )
	).

% count occurences of Ex in list-of-lists List, return in Count
count_all(List, Ex, Count) :-
	( foreach(El, List), param(Ex), fromto(0, S1, S2, Count) do
		count(El, Ex, C),
		S2 is S1 + C
	).

% rectangle R1 shouldn't overlap with rectangle R2
not_overlap(R1, R2) :-	
	X11 is R1[1], Y11 is R1[2], X12 is R1[3], Y12 is R1[4],
	X21 is R2[1], Y21 is R2[2], X22 is R2[3], Y22 is R2[4],
	(Y22 #<= Y11) #\/ (X21 #>= X12) #\/ (X22 #<= X11) #\/ (Y21 #>= Y12).

% each rectangle should not overlap with each other rectangle
not_overlapping(Rects, Max) :-
	( for(I,1,Max), param(Rects, Max) do
		( for(J,1,Max), param(I, Rects) do
			( I \= J -> 
				R1 is Rects[I],
				R2 is Rects[J],
				not_overlap(R1,R2) 
			; 
				true 
			)
		)
	).

% speed tests
speed(Nr) :-
	Methods = [anti_first_fail, smallest, first_fail, largest, occurence, most_constrained, input_order],
	Choices = [indomain, indomain_min, indomain_split, indomain_interval],
	( foreach(Selection, Methods), param(Choices, Nr) do 
		( foreach(Choice, Choices), param(Selection, Nr) do 
			writeln([Choice, Selection]),
			profile(solve(Nr, _, _, Selection, Choice, 91, 60))
		)
	).

% main solve routine
solve(Nr, Rects, Total, Selection, Choice, Method, Optimal, Timeout) :-
	problem(Nr, Max, W, H, Field),
	%prettyprint(Field, Max),
	% setup constraints for the greenhouses: each greenhouse represented by the topleft and bottom right corners as a list [X1, Y1, X2, Y2]
	dim(Rects, [Max, 4]),
	dim(Costs, [Max]),
	( for(K,1,Max), param(Rects, Costs, W, H, Max, Field) do
		% top left: X1, Y1
		Rects[K,1] :: 0..W, 
		Rects[K,2] :: 0..H, 
		% bottom right: X2, Y2
		Rects[K,3] :: 0..W + 1,
		Rects[K,4] :: 0..H + 1,
		% both coordinates of the greenhouse are 0 or >= 1
		((Rects[K,1] #>= 1) #/\ (Rects[K,2] #>= 1) #/\ (Rects[K,3] #>= 1) #/\ (Rects[K,4] #>= 1)) #\/ ((Rects[K,1] #= 0) #/\ (Rects[K,2] #= 0) #/\ (Rects[K,3] #= 0) #/\ (Rects[K,4] #= 0)),
		% each rect should have bottom right > top left
		((Rects[K,3] #> Rects[K,1]) #/\ (Rects[K,4] #> Rects[K,2])) #\/ ((Rects[K,3] #= 0) #/\ (Rects[K,1] #= 0) #/\ (Rects[K,4] #= 0) #/\ (Rects[K,2] #= 0)),
		% costs of each greenhouse
		((Rects[K,3] - Rects[K,1]) #> 0) #/\ ((Rects[K,4] - Rects[K,2]) #> 0) #<=> (Costs[K] #<=> 10 + (Rects[K,3] - Rects[K,1]) * (Rects[K,4] - Rects[K,2])),
		((Rects[K,3] - Rects[K,1]) #= 0) #/\ ((Rects[K,4] - Rects[K,2]) #= 0) #<=> (Costs[K] #<=> 0),
		% all strawberries must be covered by the greenhouse
		( foreach(Row, Field), param(Rects, Max, W), count(J,1,H) do
			( foreach(Cell, Row), param(Rects, J, Max), count(I,1,W) do				
				( Cell = 1 -> covered(I, J, Rects, Max) ; true )
			)
		)
	),
	% greenhouses shouldn't overlap
	not_overlapping(Rects, Max),
	% setup the search
	collection_to_list(Rects, RectsList),
	% setup the minimization objective
	collection_to_list(Costs, CostsList),
	sumlist(CostsList, Total),
	% do the actual search
	minimize(search(RectsList, 0, Selection, Choice, Method, []), Total, Optimal, 1000, 0, Timeout),
	% alternative calls
	%minimize(ilabeling(RectsList), Total, Optimal, 1000, 0, Timeout),
	%minimize(plabeling(RectsList), Total),
	% show the result as required
	show(Rects, Field, Total, Max, W, H).

% test, parallel labelings
plabeling([]).
plabeling([Var|Rest]) :-
	par_indomain(Var),
	labeling(Rest).

% instrumented labeling, counts nr of backtracks
ilabeling(AllVars) :-
	init_backtracks,
	( foreach(Var, AllVars) do
		count_backtracks, % insert this before choice!
		indomain(Var)
	),
	get_backtracks(B),
	printf("Solution found after %d backtracks%n", [B]).

:- local variable(backtracks), variable(deep_fail).

init_backtracks :-
	setval(backtracks,0).

get_backtracks(B) :-
	getval(backtracks,B).

count_backtracks :-
	setval(deep_fail,false).

count_backtracks :-
	getval(deep_fail,false), % may fail
	setval(deep_fail,true),
	incval(backtracks),
	fail.