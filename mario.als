module mario

--assinaturas

sig mario {
	state: one mario_state
}
--estado abstrato
abstract sig mario_state {
}
--mario pequeno
sig little_mario extends mario_state {
}
--mario grande
sig big_mario extends mario_state {
}
--mario fogo
sig fire_mario extends mario_state {
} 
--mario capa
sig cape_mario extends mario_state {
} 
--mario invencivel
sig invencible_mario extends mario_state {
}
--mario morto
sig dead_mario extends mario_state {
} 

--fatos
fact {

    --Só existe um mário
	#mario = 1

    --Só existe um estado para cada mário
	all ms: mario_state | one ms.~state 
	
    --TODO:
	--Todo mario começa pequeno
    --Um state para outro
	--Toma dano volta para mario pequeno
	--Apenas mario pequeno pode ir pra morto
}

pred show[]{
}

run show for 5
