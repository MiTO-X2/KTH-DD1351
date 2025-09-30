% ?- T = f(a,Y,Z), T = f(X,X,b).
% T = f(a, a, b),
% Y = X, X = a,
% Z = b.

/************************************************************************************************
Förklaring:
Prolog försöker göra de två termerna f(a, Y, Z) och f(X, X, b) identiska genom unifiering.

Första argumentet: a = X ⇒ X = a

Andra argumentet: Y = X ⇒ Y = a

Tredje argumentet: Z = b

Alla bindningar är konsekventa, vilket gör att termerna blir identiska: T = f(a, a, b).
************************************************************************************************/