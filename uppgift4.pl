% --- Graph definition ---

% edges
edge(a, b).
edge(a, c).
edge(b, d).
edge(c, d).
edge(d, e).

% connected/2 treats the graph as undirected
connected(X, Y) :- edge(X, Y).
connected(X, Y) :- edge(Y, X).

% --- Path predicate ---

% path(Start, End, Path) - finds a path from Start to End
path(A, B, Path) :-
    path(A, B, [A], Path).  % Visited list starts with A

% Base case: reached destination
path(A, A, _, [A]).

% Recursive case: go to neighbor N not yet visited
path(A, B, Visited, [A|Path]) :-
    connected(A, N),
    \+ member(N, Visited),
    path(N, B, [N|Visited], Path).

