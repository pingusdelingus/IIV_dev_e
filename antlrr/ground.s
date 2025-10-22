tff(semantics, logic, ($alethic_modal) == ([($domains) == ($constant),($designation) == ($rigid),($terms) == ($local),($modalities) == ($modal_system_M)])).

tff(fruit_type, type, fruit: $tType).

tff(apple_decl, type, apple: fruit).
tff(banana_decl, type, banana: fruit).
tff(healthy_decl, type, healthy: ((fruit) > $o)).
tff(rotten_decl, type, rotten: ((fruit) > $o)).

tff(d_fruit_decl, type, d_fruit: $tType).
tff(d2fruit_decl, type, d2fruit: d_fruit > fruit).
tff(d_fruit_0_decl, type, d_fruit_0: d_fruit).
tff(d_fruit_1_decl, type, d_fruit_1: d_fruit).

tff(world_0_decl, type, world_0: $world).
tff(world_1_decl, type, world_1: $world).
tff(world_2_decl, type, world_2: $world).
tff(world_3_decl, type, world_3: $world).
tff(world_4_decl, type, world_4: $world).
tff(world_5_decl, type, world_5: $world).
tff(world_6_decl, type, world_6: $world).

tff(model_worlds, interpretation-worlds, 
((! [W: $world] : ( (W = world_0) | (W = world_1) | (W = world_2) | (W = world_3) | (W = world_4) | (W = world_5) | (W = world_6) ))
& $distinct(world_0, world_1, world_2, world_3, world_4, world_5, world_6)
& ($local_world = world_5)

& $accessible_world(world_0, world_1)
& $accessible_world(world_0, world_2)
& $accessible_world(world_0, world_3)
& $accessible_world(world_0, world_4)
& $accessible_world(world_0, world_5)
& $accessible_world(world_0, world_6)

& $accessible_world(world_1, world_1)
& $accessible_world(world_1, world_2)
& $accessible_world(world_1, world_3)
& $accessible_world(world_1, world_4)
& $accessible_world(world_1, world_5)
& $accessible_world(world_1, world_6)

& $accessible_world(world_2, world_1)
& $accessible_world(world_2, world_2)
& $accessible_world(world_2, world_3)
& $accessible_world(world_2, world_4)
& $accessible_world(world_2, world_5)
& $accessible_world(world_2, world_6)

& $accessible_world(world_3, world_1)
& $accessible_world(world_3, world_2)
& $accessible_world(world_3, world_3)
& $accessible_world(world_3, world_4)
& $accessible_world(world_3, world_5)
& $accessible_world(world_3, world_6)

& $accessible_world(world_4, world_1)
& $accessible_world(world_4, world_2)
& $accessible_world(world_4, world_3)
& $accessible_world(world_4, world_4)
& $accessible_world(world_4, world_5)
& $accessible_world(world_4, world_6)


& $accessible_world(world_5, world_1)
& $accessible_world(world_5, world_2)
& $accessible_world(world_5, world_2)
& $accessible_world(world_5, world_3)
& $accessible_world(world_5, world_4)
& $accessible_world(world_5, world_5)


& $accessible_world(world_6, world_1)
& $accessible_world(world_6, world_2)
& $accessible_world(world_6, world_3)
& $accessible_world(world_6, world_4)
& $accessible_world(world_6, world_5)
& $accessible_world(world_6, world_6)

)).

tff(model_domains, interpretation-domains,
($distinct(d_fruit_0, d_fruit_1)
& (! [W: $world]: ($in_world(W,
	((! [O: fruit]: (? [DO: d_fruit]: O = d2fruit(DO)))
	& (! [DO1: d_fruit, DO2: d_fruit]: ( (d2fruit(DO1) = d2fruit(DO2)) => (DO1 = DO2) ))
	& (! [DO: d_fruit]: ( (DO = d_fruit_0) | (DO = d_fruit_1) ))
	& (? [DO: d_fruit]: (DO = d_fruit_0))
	& (? [DO: d_fruit]: (DO = d_fruit_1))))))
)).


tff(model_mapping, interpretation-mappings,
($in_world(world_0,
	((apple = d2fruit(d_fruit_0))
	& (banana = d2fruit(d_fruit_1))
	& (! [V1: fruit]: healthy(V1))
	& (! [V1: fruit]: ~(rotten(V1)))))
& $in_world(world_1,
	((apple = d2fruit(d_fruit_0))
	& (banana = d2fruit(d_fruit_1))
	& (! [V1: fruit]: healthy(V1))
	& (! [V1: fruit]: ~(rotten(V1)))))
& $in_world(world_2,
	((apple = d2fruit(d_fruit_0))
	& (banana = d2fruit(d_fruit_1))
	& (! [V1: fruit]: healthy(V1))
	& (! [V1: fruit]: ~(rotten(V1)))))
& $in_world(world_3,
	((apple = d2fruit(d_fruit_0))
	& (banana = d2fruit(d_fruit_1))
	& (! [V1: fruit]: healthy(V1))
	& (! [V1: fruit]: ~(rotten(V1)))))
& $in_world(world_4,
	((apple = d2fruit(d_fruit_0))
	& (banana = d2fruit(d_fruit_1))
	& (! [V1: fruit]: healthy(V1))
	& (! [V1: fruit]: ~(rotten(V1)))))
& $in_world(world_5,
	((apple = d2fruit(d_fruit_0))
	& (banana = d2fruit(d_fruit_1))
	& (! [V1: fruit]: healthy(V1))
	& rotten(d2fruit(d_fruit_1))
	& (! [V1: fruit]: (~((V1 = d2fruit(d_fruit_1))) => ~rotten(V1)))))
& $in_world(world_6,
	((apple = d2fruit(d_fruit_0))
	& (banana = d2fruit(d_fruit_1))
	& (! [V1: fruit]: healthy(V1))
	& (! [V1: fruit]: ~(rotten(V1)))))
)).
