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
