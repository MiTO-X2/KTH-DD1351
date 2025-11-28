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
