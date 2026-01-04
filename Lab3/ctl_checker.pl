% ctl_checker.pl
% CTL model checker implementing the proof system described in the lab.

%%%% Entry point: read input file as in skeleton %%%%
verify(Input) :-
    see(Input), 
    read(T), 
    read(L), 
    read(S), 
    read(F), 
    seen,
    check(T, L, S, [], F).

%%%% check(T, L, S, U, F) %%%%
% T - transitions (adjacency lists)
% L - labeling
% S - current state
% U - visited states used for loop detection in unfolding G/F rules
% F - CTL formula to check

% ---------------------
% Literals (atoms and negation)
% ---------------------
check(_, L, S, [], P) :-
    atom(P),
    member([S, Atoms], L),
    member(P, Atoms).        % rule 1

check(_, L, S, [], neg(P)) :-
    atom(P),
    member([S, Atoms], L),
    \+ member(P, Atoms).     % rule 2

% ---------------------
% Boolean connectives
% ---------------------
check(T, L, S, [], and(F, G)) :-
    check(T, L, S, [], F),       % rule 3 left
    check(T, L, S, [], G).       % rule 3 right

check(T, L, S, [], or(F, _G)) :-
    check(T, L, S, [], F).       % rule 4 (left)

check(T, L, S, [], or(_F, G)) :-
    check(T, L, S, [], G).       % rule 5 (right)

% ---------------------
% AX (for all next)
% ---------------------
check(T, L, S, [], ax(F)) :-
    successors(T, S, Succs),
    Succs \= [],                        
    all_check_on_list(T, L, Succs, [], F).

% ---------------------
% EX (exists next)
% ---------------------
check(T, L, S, [], ex(F)) :-
    successors(T, S, Succs),
    member(Succ, Succs),
    check(T, L, Succ, [], F).

% ---------------------
% AG (for all globally)
% AG1: if S in U -> success
% AG2: otherwise check phi at S and all successors for AG with U' = [S|U]
% ---------------------
check(_T, _L, S, U, ag(_F)) :-
    member(S, U), !.    % rule 7 (AG1): loop means success

check(T, L, S, U, ag(F)) :-
    \+ member(S, U),
    check(T, L, S, [], F),                          % need phi at S
    successors(T, S, Succs),
    Succs \= [],
    NewU = [S | U],
    all_check_on_list(T, L, Succs, NewU, ag(F)).

% ---------------------
% AF (for all eventually)
% AF1: if phi holds now -> success
% AF2: otherwise if S in U -> failure (cut out), else require AF on all successors
% ---------------------
check(T, L, S, _U, af(F)) :-
    check(T, L, S, [], F), !.   % AF1 (immediate success)

check(_T, _L, S, U, af(_F)) :-
    member(S, U), !, fail.      % encountering loop -> failure for AF

check(T, L, S, U, af(F)) :-
    \+ member(S, U),
    successors(T, S, Succs),
    Succs \= [],                % if no successors and phi not true -> fail
    NewU = [S | U],
    all_check_on_list(T, L, Succs, NewU, af(F)).  % AF2

% ---------------------
% EG (exists globally)
% EG1: if S in U -> success
% EG2: otherwise phi must hold at S and there must exist a successor leading to EG
% ---------------------
check(_T, _L, S, U, eg(_F)) :-
    member(S, U), !.           % EG1 (loop -> success)

check(T, L, S, U, eg(F)) :-
    \+ member(S, U),
    check(T, L, S, [], F),                          % phi holds now
    successors(T, S, Succs),
    Succs \= [],                                    % need at least one successor to continue infinite path
    NewU = [S | U],
    member(Succ, Succs),
    check(T, L, Succ, NewU, eg(F)).                % EG2 (existential continuation)

% ---------------------
% EF (exists eventually)
% EF1: if phi holds now -> success
% EF2: otherwise if S in U -> failure, else there must exist a successor satisfying EF
% ---------------------
check(T, L, S, _U, ef(F)) :-
    check(T, L, S, [], F), !.   % EF1

check(_T, _L, S, U, ef(_F)) :-
    member(S, U), !, fail.      % encountering loop -> failure for EF

check(T, L, S, U, ef(F)) :-
    \+ member(S, U),
    successors(T, S, Succs),
    Succs \= [],
    NewU = [S | U],
    member(Succ, Succs),
    check(T, L, Succ, NewU, ef(F)).  % EF2 (existential continuation)

% ---------------------
% Helpers
% ---------------------

% successors(+T, +S, -Succs)
% Find adjacency list for S in T, return Succs (empty list if missing)
successors(T, S, Succs) :-
    member([S, Succs], T), !.

successors(_, _, []).    % if state not found → no successors


% all_check_on_list(+T, +L, +ListOfStates, +U, +Formula)
% true iff check(T,L,s_i,U,Formula) holds for all s_i in ListOfStates
all_check_on_list(_, _, [], _U, _F).
all_check_on_list(T, L, [S1|Rest], U, F) :-
    check(T, L, S1, U, F),
    all_check_on_list(T, L, Rest, U, F).
