#lang teachlog/ugly

% Relations
rel family/2.    % Two people are family
rel familyOf/2.  % Equivalence version of family/2

rel friend/2.    % Two people are friends
rel friendOf/2.  % Symmetric version of friend/2

rel knows/2.     % Two people know each other
rel connected/2. % There is some path of relationships between two people

% Facts
family("Homer", "Marge").
family("Homer", "Bart").
family("Homer", "Lisa").
family("Homer", "Maggie").
family("Marge", "Selma").
family("Marge", "Patty").

friend("Homer", "Moe").
friend("Homer", "Barney").
friend("Bart", "Milhouse").
friend("Groundskeeper Willie", "Principal Skinner").

% Rules
familyOf(X, Y) :- family(X, Y).
familyOf(X, Y) :- family(Y, X).
familyOf(X, Z) :- family(X, Y), familyOf(Y, Z).

friendOf(X, Y) :- friend(X, Y).
friendOf(X, Y) :- friend(Y, X).

knows(X, Y) :- familyOf(X, Y).
knows(X, Y) :- friendOf(X, Y).

connected(X, Y) :- knows(X, Y).
connected(X, Z) :- knows(X, Y), knows(Y, Z). % Depth=2 to prevent infinite loop I don't understand.

% Queries
familyOf("Homer", X)?
next. next. next. next. next.

knows("Homer", "Lisa")?
knows("Homer", "Moe")?

knows("Homer", "Milhouse")?
knows("Homer", "Groundskeeper Willie")?

connected("Homer", "Milhouse")?
connected("Homer", "Groundskeeper Willie")?
