
#define MAX_X 4
#define MAX_Y 4

#define SOIL_STEP 3
#define SOIL_DELAY 15
#define SOIL_MAX 50

#define MOVE_DELAY 1
#define CLEAN_DELAY 5

#define MAX_TIME 50

#define SELECT 0
#define MOVE 1
#define CLEAN 2

typedef tag{
  pid occupiedby;
  bool occupied = false;
  bool reserved = false;
  int soilinglevel = 0

};

typedef tagrow{
  tag row[MAX_Y];
};

tagrow tags[MAX_X];

int globaltime=0;
pid globalupdater;

inline sync(timer){
    if
    ::(globaltime < MAX_TIME && timer > globaltime && globalupdater != _pid) ->   
      globaltime = timer; 
      globalupdater = _pid;
    ::else -> skip;
    fi
}
inline soil(){
    do
    :: (i < MAX_X) ->
      do
      ::(j < MAX_Y) ->
            tags[i].row[j].soilinglevel = tags[i].row[j].soilinglevel + SOIL_STEP;
            j++;
      ::(j>=MAX_Y) ->break;
      od;
      i++;
      j = 0;
    :: (i >= MAX_X) -> i=0; j=0; break;
    od;
    
}

proctype soiling(){
    int i=0;
    int j =0;
    int timer = -1;

    do
    ::(timer > MAX_TIME) -> break;
    ::(timer <= MAX_TIME && timer < globaltime) -> 
      atomic{
        soil(); 
        timer = timer + SOIL_DELAY;
        sync(timer);
      }
    ::(timer >= globaltime) -> skip;
	od;
}


inline select_tag(x, y){
    i= -1;
    j= -1;
    do
    :: (i < 2) ->
      do
      ::(j < 2 
            && x + i < MAX_X 
            && y + j < MAX_Y 
            && x + i >= 0 
            && y + j >= 0 && tags[x+i].row[y+j].occupied == false  
            && tags[x+i].row[y+j].soilinglevel > tags[x].row[y].soilinglevel) ->
          currentx = x+i;
          currenty = y+j;
          j = j + 1;
      :: (j < 2 && 
            !(x + i < MAX_X 
            && y + j < MAX_Y 
            && x + i >= 0 
            && y + j >= 0 && tags[x+i].row[y+j].occupied == false  
            && tags[x+i].row[y+j].soilinglevel > tags[x].row[y].soilinglevel))->
          j = j + 1;
      ::(j >= 2) ->break;
      od;
      j = -1; 
      i = i + 1;
    :: (i >= 2) -> break;
    od;
}

proctype agent(){
    /*default starting location*/
    byte x = 0;
    byte y = 0;
    byte currentx = 0;
    byte currenty = 0;
    int timer = 0;
    int i;
    int j;

    byte status = SELECT;

    x = 0;
    y = 0;
    do
    ::(timer > MAX_TIME) -> break;
    ::(timer <= MAX_TIME && timer > globaltime) ->skip;
    ::(timer <= MAX_TIME && timer <= globaltime) ->
        if
        :: (status == MOVE) ->
          atomic{
            tags[x].row[y].occupied = false;
            x = currentx;
            y = currenty;
            tags[x].row[y].occupied = true;
            status = SELECT;
          }
        :: (status == CLEAN) ->
          atomic{
            tags[x].row[y].soilinglevel = 0;
            status = SELECT;
          }
        ::(status == SELECT) -> 
          atomic{
            currentx = x;
            currenty = y;
            select_tag(x,y);
          }
          if
            :: (currentx == x && currenty == y) ->
              atomic{
                timer = timer + CLEAN_DELAY;
                status = CLEAN;
              }
            :: else -> 
              atomic{
                timer = timer + MOVE_DELAY;
                status = MOVE;
              }
          fi;
          atomic{
            sync(timer);
          }
        fi

    od

}
never{
T0_init:
        if
        :: (tags[0].row[0].soilinglevel <= SOIL_MAX
            && tags[0].row[1].soilinglevel <= SOIL_MAX
            && tags[0].row[2].soilinglevel <= SOIL_MAX
            && tags[0].row[3].soilinglevel <= SOIL_MAX
            && tags[1].row[0].soilinglevel <= SOIL_MAX
            && tags[1].row[1].soilinglevel <= SOIL_MAX
            && tags[1].row[2].soilinglevel <= SOIL_MAX
            && tags[1].row[3].soilinglevel <= SOIL_MAX
            && tags[2].row[0].soilinglevel <= SOIL_MAX
            && tags[2].row[1].soilinglevel <= SOIL_MAX
            && tags[2].row[2].soilinglevel <= SOIL_MAX
            && tags[2].row[3].soilinglevel <= SOIL_MAX
            && tags[3].row[0].soilinglevel <= SOIL_MAX
            && tags[3].row[1].soilinglevel <= SOIL_MAX
            && tags[3].row[2].soilinglevel <= SOIL_MAX
            && tags[3].row[3].soilinglevel <= SOIL_MAX
            ) -> goto T0_init
        fi;

}

init{
  atomic{
    run soiling();
    run agent();
    run agent();
  }
}
