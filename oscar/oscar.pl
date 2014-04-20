/*
 *      oscar.pl
 *
 *		Students edit this program to complete the assignment.
 */

:-consult(wp).

candidate_number(17655).

map_object(c(_), p(_, _)).
map_object(o(_), p(_, _)).

object_path(map_object(_, _), Path) :-
	is_list(Path).

objects_list(Oracles, Chargers) :-
	is_list(Oracles),
	is_list(Chargers).

path(Depth, Path) :-
	integer(Depth),
	is_list(Path).

solve_task(Task,Cost):-
	agent_current_position(oscar,P),
	%solve_task_bt(Task,[c(0,P),P],0,R,Cost,_NewPos),!,	% prune choice point for efficiency
	solve_task_top(Task,[[c(0,P), P]],R,Cost,_NewPos),
	reverse(R,[_Init|Path]),
	agent_do_moves(oscar,Path).

solve_task_top(go(Target),[[c(0,P), P]],R,Cost,NewPos) :-
    map_distance(P, Target, Dist),
	empty_assoc(SearchedList),
    solve_task_astar(go(Target),[[Dist, c(0,P), P]],R,Cost,NewPos, SearchedList).

solve_task_top(adjacent(Target),[[c(0,P), P]],R,Cost,NewPos) :-
    map_distance(P, Target, Dist),
	empty_assoc(SearchedList),
    solve_task_astar(adjacent(Target),[[Dist, c(0,P), P]],R,Cost,NewPos, SearchedList).

solve_task_top(Task,[[c(0,P), P]],R,Cost,NewPos) :-
	empty_assoc(SearchedList),
    solve_task_bf(Task,[[c(0,P), P]],R,Cost,NewPos,SearchedList).

%% backtracking depth-first search, needs to be changed to agenda-based A*
solve_task_bt(Task,Current,Depth,RPath,[cost(Cost),depth(Depth)],NewPos) :-
	achieved(Task,Current,RPath,Cost,NewPos).
solve_task_bt(Task,Current,D,RR,Cost,NewPos) :-
	Current = [c(F,P)|RPath],
	search(P,P1,R,C),
	\+ memberchk(R,RPath), % check we have not been here already
	D1 is D+1,
	F1 is F+C,
	solve_task_bt(Task,[c(F1,P1),R|RPath],D1,RR,Cost,NewPos). % backtracking search

solve_task_astar(Task,Current,RPath,CostList,NewPos,_) :-
   % Because this is bf the first item in RPath will always be the shortest
   Current = [CurList | _],
   CurList = [ _ | Cur],
   Cur = [c(Depth, _) | _],
   CostList = [cost(Cost), depth(Depth)],
   achieved(Task,Cur,RPath,Cost,NewPos).
solve_task_astar(Task,Current,RR,Cost,NewPos,SearchedList) :-
   Current = [CurList | OtherRPaths],
   CurList = [_ | Cur],
   Cur = [c(_,P)|RPath],
   children(P, Children, RPath, SearchedList),
   populate_searched_list(SearchedList, Children, NewSearchedList),
   (Task = go(Pos) -> Target = Pos; Task = adjacent(Pos) -> Target = Pos),
   calc_children_costs_astar(Target, Cur, Children, ChildrenCosts),
   append(OtherRPaths, ChildrenCosts, NewRPath),
   sort(NewRPath, SortedRPath),
   solve_task_astar(Task, SortedRPath, RR, Cost, NewPos, NewSearchedList).

% (Children, [c(C,P),P])
calc_children_costs_astar(Target, Cur, Children, ChildCosts) :-
   do_children_costs_astar(Target, Cur, Children, [], ChildCosts).

do_children_costs_astar(_, _, [], ChildCosts, ChildCosts).
do_children_costs_astar(Target, Cur, [Child|Children], PastCosts, ChildCosts) :-
   Cur = [c(OldDepth, _)|RPath],
   Depth is OldDepth+1,
   map_distance(Child, Target, Dist),
   do_children_costs_astar(Target, Cur, Children, [[Dist, c(Depth, Child) | [Child|RPath]] | PastCosts], ChildCosts).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Finds a list of objects that we haven't already found.
%% In the case of oracles they haven't already been visited.
%% @param FoundObjects [map_object]: A list of objects we already know about
%% @returns MapObjects [map_object]: The existing list of objects with the new
%list appended to it
%% @param CurPos p: Current agent position
%% @returns OraclePath [p]: The path to the nearest oracle
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
do_find_stuff(FoundObjects, MapObjects, CurPos, OraclePath, SearchedFrom) :-
	do_command([oscar, console, 'Searching...']),
	empty_assoc(SearchedList),
	find_stuff(FoundObjects, MapObjects, [path(0, [CurPos])], OraclePath, SearchedList, SearchedFrom),
	do_command([oscar, console, 'Done searching']),
	!.

find_stuff(MapObjects, MapObjects, Paths, OraclePath, _, SearchedFrom) :-
	Paths = [NextPath | _],
	NextPath = path(Depth, _),
	Depth >= 20, % Limits the search depth to 20
	(var(OraclePath) -> do_find_good_outer_path(Paths, 20, SearchedFrom, GoodPath),
		OraclePath = GoodPath
	; true
	),
	!.
find_stuff(FoundObjects, MapObjects, Paths, OraclePath, SearchedList, SearchedFrom) :-
	Paths = [CurPath | OtherPaths],
	CurPath = path(_, [CurPos | RestOfPath]),
	% Find the empty spaces around us (That aren't already in this path)
	children(CurPos, Children, RestOfPath, SearchedList),
	populate_searched_list(SearchedList, Children, NewSearchedList),
	calc_children_costs(CurPath, Children, ChildrenCosts),
	append(OtherPaths, ChildrenCosts, NewPaths),
	% Find the oracles and stations around us that we don't already know about
	FoundObjects = objects_list(Oracles, Chargers),
	child_oracles(CurPos, NewOracles, Oracles),
	% Set the Oracle path if we found an oracle and the path hasn't been set
	% already
	((NewOracles = [_|_], var(OraclePath)) -> OraclePath = CurPath
	; true),
	child_chargers(CurPos, NewChargers, Chargers),
	append(Oracles, NewOracles, FoundOracles),
	append(Chargers, NewChargers, FoundChargers),
	% Continue recursing
	find_stuff(objects_list(FoundOracles, FoundChargers), MapObjects, NewPaths, OraclePath, NewSearchedList, SearchedFrom).

populate_searched_list(NewAssoc, [], NewAssoc).
populate_searched_list(Assoc, [Child | Children], ReturnAssoc) :-
	put_assoc(Child, Assoc, 1, NewAssoc),
	populate_searched_list(NewAssoc, Children, ReturnAssoc).

do_find_good_outer_path(Paths, DepthLim, SearchedFrom, GoodPath) :-
	DepthGuess is DepthLim / 2,
	(find_good_outer_path(Paths, DepthGuess, SearchedFrom, ReturnedPath) ->
		GoodPath = ReturnedPath
		% Not a great path but we can't find anything better
		% TODO: Maybe pick a random long path instead
	; Paths = [GoodPath | _ ]
	).

find_good_outer_path([Path | Paths], Radius, SearchedFrom, PathToReturn) :-
	(path_is_good(Path, SearchedFrom, Radius) -> PathToReturn = Path
	; find_good_outer_path(Paths, Radius, SearchedFrom, PathToReturn)
	).

path_is_good(_, [], _).
path_is_good(Path, [NextPos | SearchedFrom], Radius) :-
	Path = path(_, [EndPos | _]),
	EndPos = p(MaybeX, MaybeY),
	NextPos = p(FromX, FromY),
	(MaybeX < FromX - Radius ; MaybeX > FromX + Radius),
	(MaybeY < FromY - Radius ; MaybeY > FromY + Radius),
	path_is_good(Path, SearchedFrom, Radius).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Finds all the unqueried oracles around us that we don't already know about
%% @param Pos p: The position to search around
%% @returns NewOracles [map_object]: The list of oracles we found
%% @param OldOracles [map_object]: The list of oracles we already know about
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
child_oracles(Pos, NewOracles, OldOracles) :-
	findall(map_object(o(OID), NewPos), map_adjacent(Pos, NewPos, o(OID)), AllOracles),
	% Filter out those that have been queried
	filter_oracles(AllOracles, [], NonVisitedOracles),
	% Filter out those that we already know about
	do_filter_objects(NonVisitedOracles, OldOracles, NewOracles).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Finds all the unqueried chargers around us that we don't already know about
%% @param Pos p: The position to search around
%% @returns NewChargers [map_object]: The list of chargers we found
%% @param OldChargers [map_object]: The list of chargers we already know about
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
child_chargers(Pos, NewChargers, OldChargers) :-
	findall(map_object(c(CID), NewPos), map_adjacent(Pos, NewPos, c(CID)), AllChargers),
	% Filter out those that we already know about
	do_filter_objects(AllChargers, OldChargers, NewChargers).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Filters the objects out of Unfiltered that already exist in ExistingObjs
%% @param Unfiltered []: The list of objects to filter
%% @param ExistingObjs []: The list of objects to filter out of Unfiltered
%% @returns Filtered []: The filtered list
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
do_filter_objects(Unfiltered, ExistingObjs, Filtered) :-
	filter_objects(Unfiltered, ExistingObjs, [], Filtered).

filter_objects([], _, Filtered, Filtered).
filter_objects([Next | OtherObjs], ExistingObjs, Filtered, Valids) :-
	( memberchk(Next, ExistingObjs) ->
		filter_objects(OtherObjs, ExistingObjs, Filtered, Valids)
	;  filter_objects(OtherObjs, ExistingObjs, [Next | Filtered], Valids)
	).

solve_task_bf(Task,Current,RPath,CostList,NewPos,_) :-
   % Because this is bf the first item in RPath will always be the shortest
   Current = [Cur | _],
   Cur = [c(Depth, _) | _],
   CostList = [cost(Cost), depth(Depth)],
   achieved(Task,Cur,RPath,Cost,NewPos).
solve_task_bf(Task,Current,RR,Cost,NewPos,SearchedList) :-
   Current = [Cur | OtherRPaths],
   Cur = [c(_,P)|RPath],
   children(P, Children, RPath, SearchedList),
   populate_searched_list(SearchedList, Children, NewSearchedList),
   calc_children_costs(Cur, Children, ChildrenCosts),
   append(OtherRPaths, ChildrenCosts, NewRPath),
   solve_task_bf(Task, NewRPath, RR, Cost, NewPos, NewSearchedList).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Finds all of the empty positions around Current that haven't already been
%visited.
%% @param Current p: The position to search around
%% @returns Children [p]: The empty positions around Current
%% @param RPath [p]: The already visited positions in this path
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
children(Current, Children, RPath, SearchedList) :-
   findall(NewPos, map_adjacent(Current, NewPos, empty), AllChildren),
   filter_children(AllChildren, RPath, Children, SearchedList).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Calculates the path to and the cost of a position around the current one
%% @param Cur path: The path to the current position
%% @param Children [p]: The positions surround the current one
%% @returns ChildCosts [path]: The paths to the Children positions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
calc_children_costs(Cur, Children, ChildCosts) :-
   do_children_costs(Cur, Children, [], ChildCosts).

do_children_costs(_, [], ChildCosts, ChildCosts).
do_children_costs(CurPath, [Child|Children], PastCosts, ChildCosts) :-
   CurPath = path(OldDepth, Path),
   Depth is OldDepth+1,
   do_children_costs(CurPath, Children, [path(Depth, [Child | Path]) | PastCosts], ChildCosts).

achieved(go(Exit),Current,RPath,Cost,NewPos) :-
	Current = [c(Cost,NewPos)|RPath],
	( Exit=none -> true
	; otherwise -> RPath = [Exit|_]
	).
achieved(find(O),Current,RPath,Cost,NewPos) :-
	Current = [c(Cost,NewPos)|RPath],
	( O=none    -> true
	; otherwise -> RPath = [Last|_],map_adjacent(Last,_,O)
	).
achieved(adjacent(P),Current,RPath,Cost,NewPos) :-
	Current = [c(Cost,NewPos)|RPath],
	( P=none    -> true
	; otherwise -> RPath = [Last|_],map_adjacent(Last,P,_)
	).

search(F,N,N,1):-
	map_adjacent(F,N,empty).

filter_children(Children, RPath, Valids, SearchedList) :-
   filter_loop(Children, RPath, [], Valids, SearchedList).

filter_loop([], _, Valids, Valids, _).
filter_loop([Child|Children], RPath, Filtered, Valids, SearchedList) :-
   (\+ memberchk(Child, RPath), \+ get_assoc(Child, SearchedList, _) ->
      filter_loop(Children, RPath, [Child|Filtered], Valids, SearchedList)
   ; filter_loop(Children, RPath, Filtered, Valids, SearchedList)
   ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% A data structure containing the actor name and it's links
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
actor_data(actor_name, Links) :-
   actor(actor_name),
   is_list(Links).

find_identity(A):-
   findall(A, actor(A), ActorNames),
   create_actor_data(ActorNames, Actors),
   keep_filtering_actors(Actors, Actor, objects_list([],[]), []),
   Actor = actor_data(A, _),
   !.

keep_filtering_actors([Actor], Actor, _, _).
keep_filtering_actors(Unfiltered, Actor, FoundObjects, SearchedFrom) :-
	FoundObjects = objects_list([], _),
	recharge_if_needed(FoundObjects, _),
    agent_current_position(oscar, CurPos),
	do_find_stuff(FoundObjects, Objects, CurPos, ClosestOracle, SearchedFrom),
	NewSearchedFrom = [CurPos | SearchedFrom],
	ClosestOracle = path(_, PathFromOracle),
	reverse(PathFromOracle, [_ | PathToOracle]),
	Objects = objects_list(NewOracles, NewChargers)
	move_and_charge(CurPos, PathToOracle, NewChargers, false),
	% We don't care if this fails. do_find_stuff probably couldn't find an
	% oracle so gave us an empty space to go to instead
	(NewOracles = [map_object(Oracle, _)|RemainingOracles] ->
		agent_ask_oracle(oscar, Oracle, link, Link),
		filter_actors(Unfiltered, Link, Filtered)
	; Filtered = Unfiltered, RemainingOracles = []
	),
	keep_filtering_actors(Filtered, Actor, objects_list(RemainingOracles, NewChargers), NewSearchedFrom),
	!.

keep_filtering_actors(Unfiltered, Actor, FoundObjects, SearchedFrom) :-
	FoundObjects = objects_list(RemainingOracles, Chargers),
	recharge_if_needed(FoundObjects, _),
    agent_current_position(oscar, CurPos),
    do_get_closest_oracle(CurPos, RemainingOracles, ClosestOracle),
    ClosestOracle = map_object(Oracle, Pos),
    solve_task_top(adjacent(Pos),[[c(0,CurPos), CurPos]],PathFromOracle,_,_),
	reverse(PathFromOracle, [_ | PathToOracle]),
	move_and_charge(CurPos, PathToOracle, Chargers, false),
	agent_ask_oracle(oscar, Oracle, link, Link),
	filter_actors(Unfiltered, Link, Filtered),
	select(ClosestOracle, RemainingOracles, OraclesLeft),
	keep_filtering_actors(Filtered, Actor, objects_list(OraclesLeft, Chargers), SearchedFrom),
	!.

move_and_charge(_, [], _, _).
move_and_charge(Pos, [NextPos|Path], Chargers, Charged) :-
    agent_current_energy(oscar, Energy),
    (Charged -> NewCharged = Charged
    ; recharge_and_return(Chargers, Energy, Pos, NewCharged)),
    agent_do_move(oscar, NextPos),
    move_and_charge(NextPos, Path, Chargers, NewCharged).

recharge_and_return(_, Energy, _, false) :-
    Energy >= 70.
recharge_and_return([], _, _, false).
recharge_and_return(_, _, CurPos, true) :-
    map_adjacent(CurPos, _, c(CID)),
    agent_topup_energy(oscar, c(CID)).
recharge_and_return([Charger|Chargers], Energy, CurPos, Charged) :-
    Charger = map_object(ChargerObj, Pos),
    solve_task_top(adjacent(Pos),[[c(0,CurPos), CurPos]],PathFromStation,Cost,_NewPos),
    Cost = [cost(Dist), _],
	(Dist =< 3 -> reverse(PathFromStation, [_ | PathToStation]),
		agent_do_moves(oscar, PathToStation),
		agent_topup_energy(oscar, ChargerObj),
		agent_do_moves(oscar, PathFromStation),
		Charged = true
	; recharge_and_return(Chargers, Energy, CurPos, Charged)).

% TODO: Add to SearchedFrom
recharge_if_needed(FoundObjects, NewFoundObjects) :-
	!,
	FoundObjects = objects_list(_, Chargers),
	agent_current_energy(oscar, Energy),
	agent_current_position(oscar, CurPos),
	(recharge_if_possible(Chargers, Energy, CurPos) -> NewFoundObjects = FoundObjects
	; % Last ditch attempt to find a charger near enough
		do_find_stuff(FoundObjects, NewFoundObjects, CurPos, _, []),
		NewFoundObjects = objects_list(_, MoreChargers),
		recharge_if_possible(MoreChargers, Energy, CurPos)
	),
	!.

recharge_if_possible([Charger | Chargers], Energy, CurPos) :-
    Energy =< 30,
	Charger = map_object(ChargerObj, Pos),
	solve_task_top(adjacent(Pos),[[c(0,CurPos), CurPos]],PathFromStation,Cost,_NewPos),
	Cost = [cost(Dist), _],
	(Dist =< Energy -> reverse(PathFromStation, [_ | PathToStation]),
		agent_do_moves(oscar, PathToStation),
		agent_topup_energy(oscar, ChargerObj)
	; recharge_if_possible(Chargers, Energy, CurPos)
	).

recharge_if_possible(_, _, _).

do_get_closest_oracle(CurPos, [Oracle|Oracles], Closest):-
    Oracle = map_object(_, Pos),
    map_distance(CurPos, Pos, D),
    get_closest_oracle(CurPos, Oracles, Oracle, Closest, D).

get_closest_oracle(_, [], Closest, Closest, _).
get_closest_oracle(CurPos, [Oracle|Oracles], OldOracle, Closest, OldDistance):-
    Oracle = map_object(_, Pos),
    map_distance(CurPos, Pos, D),
    (D =< OldDistance -> NewDistance = D, NewOracle = Oracle
    ; NewDistance = OldDistance, NewOracle = OldOracle),
    get_closest_oracle(CurPos, Oracles, NewOracle, Closest, NewDistance).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Finds all of the links for the given ActorNames and puts them into actor_data
%% @param ActorNames [string]: The list of actor names
%% @returns Actors [actor_data]: The list of actor data
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
create_actor_data(ActorNames, Actors) :-
   do_create_actor_data(ActorNames, [], Actors).

do_create_actor_data([], Actors, Actors).
do_create_actor_data([CurActor|ActorNames], Processed, Actors) :-
   wp(CurActor, WT),
   findall(L, wt_link(WT, L), Links),
   do_create_actor_data(ActorNames, [actor_data(CurActor, Links)|Processed], Actors).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Filters the list of actor_data to only those which have the given link
%% @param Unfiltered [actor_data]: The list of actors to filter
%% @param Link: The link which filtered actors must all have
%% @returns Filtered: The filtered list of actors
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
filter_actors(Unfiltered, Link, Filtered) :-
   do_filter_actors(Unfiltered, Link, [], Filtered).

do_filter_actors([], _, Filtered, Filtered).
do_filter_actors([Actor|Unfiltered], Link, Filtering, Filtered) :-
   Actor = actor_data(_,Links),
   (memberchk(Link, Links) -> do_filter_actors(Unfiltered, Link, [Actor|Filtering], Filtered)
   ; do_filter_actors(Unfiltered, Link, Filtering, Filtered)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Filters a list of oracles to only those which haven't already been visited
%% @param Unfiltered [map_object]: The list of oracles to filter
%% @param Filtered []:
%% @returns Unqueried [map_object]: The list of unqueried oracles
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
filter_oracles([], Unqueried, Unqueried).
filter_oracles([Next | Unfiltered], Filtered, Unqueried) :-
	Next = map_object(Oracle, Pos),
	(agent_check_oracle(oscar, Oracle) -> filter_oracles(Unfiltered, Filtered, Unqueried)
	; filter_oracles(Unfiltered, [map_object(Oracle, Pos) | Filtered], Unqueried)
	).

%%% command shell %%%

shell:-
	get_input(Input),
	handle_input(Input).

handle_input(Input):-
	( Input = stop -> true
	; Input = reset -> ailp_reset,shell
	; Input = [H|T] -> handle_input(H),handle_input(T),shell
	; callable(Input,G,R) -> ( call(G) -> show_response(R) ; show_response('This failed.') ),shell
	; otherwise -> show_response('Unknown command, please try again.'),shell
	).

% get input from user
get_input(Input):-
	write('? '),read(Input).

% show answer to user
show_response(R):-
	( R=shell(Response)   -> writes('! '),writes(Response),writes(nl)
	; R=console(Response) -> term_to_atom(Response,A),do_command([oscar,console,A])
	; R=both(Response)    -> show_response(shell(Response)),show_response(console(Response))
	; R=agent(Response)   -> term_to_atom(Response,A),do_command([oscar,say,A])
	; R=[H|T]             -> show_response(H),show_response(T)
	; R=[]                -> true
	; otherwise           -> writes(['! ',R])
	).

writes(A):-
	( A=[]      -> nl
	; A=nl      -> nl
	; A=[H|T]   -> writes(H),writes(T)
	; A=term(T) -> write(T)
	; otherwise -> write(A)
	).

% callable(+Command, +Goal, ?Response)
callable(call(G),call(G),G).
callable(topup(S),agent_topup_energy(oscar,S),agent(topup)).
callable(energy,agent_current_energy(oscar,E),both(current_energy(E))).
callable(position,agent_current_position(oscar,P),both(current_position(P))).
callable(ask(S,Q),agent_ask_oracle(oscar,S,Q,A),A).
callable(Task,solve_task(Task,Cost),[console(Task),shell(term(Cost))]):-
	task(Task).

task(go(_Pos)).
task(adjacent(_Pos)).
task(find(_O)).	% oracle o(N) or charging station c(N)
