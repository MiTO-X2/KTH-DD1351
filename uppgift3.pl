% Simple length predicate
my_length([], 0).
my_length([_|T], N) :-
    my_length(T, N1),
    N is N1 + 1.

% Main predicate: partstring(List, Length, Substring)
partstring(List, L, F) :-
    append(_, Rest, List),   % pick a suffix Rest of List
    append(F, _, Rest),      % pick a prefix F of Rest -> contiguous
    F \= [],                 % exclude empty substring
    my_length(F, L).         % compute length of F
