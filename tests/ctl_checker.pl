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
