tff(people_worlds,interpretation-worlds,
    ( ! [W: $world] : ( W = w1 | W = w2 | W = w3 )
    & $distinct(w1,w2,w3)
    & $local_world = w1
    & $accessible_world(w1,w1) & $accessible_world(w2,w2)
    & $accessible_world(w1,w2) & $accessible_world(w2,w3)
    & $accessible_world(w3,w1) & ~ $accessible_world(w1,w3)
    & ~ $accessible_world(w2,w1) & ~ $accessible_world(w3,w2)
    & ~ $accessible_world(w3,w3) ) ).
