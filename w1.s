tff(fruit_type,type,fruit: $tType).
tff(apple_decl,type,apple: fruit).
tff(banana_decl,type,banana: fruit).
tff(healthy_decl,type,healthy: fruit > $o).
tff(rotten_decl,type,rotten: fruit > $o).

tff(d_fruit_type,type,d_fruit: $tType).
tff(d2fruit_decl,type, d2fruit: d_fruit > fruit ).
tff(d_apple_decl,type,d_apple: d_fruit).
tff(d_banana_decl,type,d_banana: d_fruit).

! [F: fruit] : ? [DF: d_fruit] : F = d2fruit(DF)
    & ! [DF: d_fruit] : ( DF = d_apple | DF = d_banana )
    & $distinct(d_apple,d_banana)
    & ? [DP: d_fruit] : ( DP = d_apple )
    & ? [DP: d_fruit] : ( DP = d_banana )
    & ! [DF1: d_fruit,DF2: d_fruit] :
        ( d2fruit(DF1) = d2fruit(DF2) => DF1 = DF2 ).

( apple = d2fruit(d_apple)
    & banana = d2fruit(d_banana)
    & healthy(d2fruit(d_apple))
    & healthy(d2fruit(d_banana)) ).

( ~ rotten(d2fruit(d_apple))
    & rotten(d2fruit(d_banana))).
