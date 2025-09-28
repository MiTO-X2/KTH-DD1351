% Base case: tom lista
remove_duplicates([], []).

% Case 1: Om huvudet är inte i svansen, behåll H
remove_duplicates([H|T], [H|Result]) :-
    \+ member(H, T),
    remove_duplicates(T, Result).

% Case 2: Om huvudet är redan i svansen, hoppa över H
remove_duplicates([H|T], Result) :-
    member(H, T),
    remove_duplicates(T, Result).
