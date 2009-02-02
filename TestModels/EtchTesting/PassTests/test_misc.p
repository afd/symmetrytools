typedef tag { pid occupiedby ; 
bool occupied = false ; 
bool reserved = false ; 
int soilinglevel = 0 } ; 
typedef tagrow { tag row [ 4 ] ; 
} ; 
tagrow tags [ 4 ] ; 
int globaltime = 0 ; 
pid globalupdater ; 
proctype soiling ( ) { byte i = 0 ; 
byte j = 0 ; 
int timer = - 1 ; 
do :: ( timer > 50 ) -> 
break ; 
:: ( timer <= 50 && timer < globaltime ) -> 
atomic { do :: ( i < 4 ) -> 
do :: ( j < 4 ) -> 
tags [ i ] . row [ j ] . soilinglevel = tags [ i ] . row [ j ] . soilinglevel + 3 ; 
j ++ ; 
:: ( j >= 4 ) -> 
break ; 
od ; 
i ++ ; 
j = 0 ; 
:: ( i >= 4 ) -> 
i = 0 ; 
j = 0 ; 
break ; 
od ; 
; 
timer = timer + 15 ; 
if :: ( globaltime < 50 && timer  > globaltime && globalupdater != _pid ) -> 
globaltime = timer  ; 
globalupdater = _pid ; 
:: else -> 
skip ; 
fi ; 
} :: ( timer >= globaltime ) -> 
skip ; 
od ; 
} proctype agent ( ) { byte x = 0 ; 
byte y = 0 ; 
byte currentx = 0 ; 
byte currenty = 0 ; 
int timer = 0 ; 
byte i ; 
byte j ; 
byte status = 0 ; 
x = 0 ; 
y = 0 ; 
do :: ( timer > 50 ) -> 
break ; 
:: ( timer <= 50 && timer > globaltime ) -> 
skip ; 
:: ( timer <= 50 && timer <= globaltime ) -> 
if :: ( status == 1 ) -> 
atomic { tags [ x ] . row [ y ] . occupied = false ; 
x = currentx ; 
y = currenty ; 
tags [ x ] . row [ y ] . occupied = true ; 
status = 0 ; 
} :: ( status == 2 ) -> 
atomic { tags [ x ] . row [ y ] . soilinglevel = 0 ; 
status = 0 ; 
} :: ( status == 0 ) -> 
atomic { currentx = x ; 
currenty = y ; 
i = 255 ; 
j = 255 ; 
do :: ( ( ( 255 == i ) || ( i < 2 ) ) ) -> 
do :: ( ( ( ( 255 == j ) || ( j < 2 ) ) ) && x  + i < 4 && y  + j < 4 && x  + i >= 0 && y  + j >= 0 && tags [ x  + i ] . row [ y  + j ] . occupied == false && tags [ x  + i ] . row [ y  + j ] . soilinglevel > tags [ x  ] . row [ y  ] . soilinglevel ) -> 
currentx = x  + i ; 
currenty = y  + j ; 
j = j + 1 ; 
:: ( ( ( ( 255 == j ) || ( j < 2 ) ) ) && ! ( x  + i < 4 && y  + j < 4 && x  + i >= 0 && y  + j >= 0 && tags [ x  + i ] . row [ y  + j ] . occupied == false && tags [ x  + i ] . row [ y  + j ] . soilinglevel > tags [ x  ] . row [ y  ] . soilinglevel ) ) -> 
j = j + 1 ; 
:: ( ( ( 255 != j ) && ( j >= 2 ) ) ) -> 
break ; 
od ; 
j = 255 ; 
i = i + 1 ; 
:: ( ( ( 255 != i ) && ( i >= 2 ) ) ) -> 
break ; 
od ; 
; 
} if :: ( currentx == x && currenty == y ) -> 
atomic { timer = timer + 5 ; 
status = 2 ; 
} :: else -> 
atomic { timer = timer + 1 ; 
status = 1 ; 
} fi ; 
atomic { if :: ( globaltime < 50 && timer  > globaltime && globalupdater != _pid ) -> 
globaltime = timer  ; 
globalupdater = _pid ; 
:: else -> 
skip ; 
fi ; 
} fi od } never { T0_init : if :: ( tags [ 0 ] . row [ 0 ] . soilinglevel <= 50 && tags [ 0 ] . row [ 1 ] . soilinglevel <= 50 && tags [ 0 ] . row [ 2 ] . soilinglevel <= 50 && tags [ 0 ] . row [ 3 ] . soilinglevel <= 50 && tags [ 1 ] . row [ 0 ] . soilinglevel <= 50 && tags [ 1 ] . row [ 1 ] . soilinglevel <= 50 && tags [ 1 ] . row [ 2 ] . soilinglevel <= 50 && tags [ 1 ] . row [ 3 ] . soilinglevel <= 50 && tags [ 2 ] . row [ 0 ] . soilinglevel <= 50 && tags [ 2 ] . row [ 1 ] . soilinglevel <= 50 && tags [ 2 ] . row [ 2 ] . soilinglevel <= 50 && tags [ 2 ] . row [ 3 ] . soilinglevel <= 50 && tags [ 3 ] . row [ 0 ] . soilinglevel <= 50 && tags [ 3 ] . row [ 1 ] . soilinglevel <= 50 && tags [ 3 ] . row [ 2 ] . soilinglevel <= 50 && tags [ 3 ] . row [ 3 ] . soilinglevel <= 50 ) -> 
goto T0_init fi ; 
} init { atomic { run soiling ( ) ; 
run agent ( ) ; 
run agent ( ) ; 
} }
   