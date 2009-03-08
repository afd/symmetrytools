#define SOIL_MAX 85

#define MOVE_DELAY 1
#define CLEAN_DELAY 5

#define MAX_TIME 80
#define MAX_X 4
#define MAX_Y 4


mtype = {SELECT,MOVE, CLEAN };

mtype = {FREE,BLOCKED};
mtype updater[5]=FREE;

typedef tag{
  pid occupiedby;
  bool occupied = false;
  bool reserved = false;
  int soilinglevel = 0

};

typedef tagrow{
  tag row[MAX_Y]
};

tagrow tags[MAX_X];

int globaltime=0;

inline sync(timer){
  if
  ::(globaltime < MAX_TIME && timer > globaltime 
      && updater[_pid] == FREE) ->
    globaltime = timer;
    updater[_pid] = BLOCKED;
    
  ::else -> skip;
  fi;
  if
  :: (updater[3] == BLOCKED && updater[1] == BLOCKED && updater[2] == BLOCKED) ->
    updater[1] = FREE;
    updater[2] = FREE;
    updater[3] = FREE;
  ::else
  fi

}

inline select_tag(x, y){
    i= 0;
    j= 0;
    do
    :: (i < 2) ->
      do
      ::(j < 2 
            && x + i < MAX_X 
            && y + j < MAX_Y 
            && x + i >= 0 
            && y + j >= 0 
            && tags[x+i].row[y+j].occupied == false
            && tags[x+i].row[y+j].reserved == false
            && tags[x+i].row[y+j].soilinglevel < tags[currentx].row[currenty].soilinglevel) ->
          tags[currentx].row[currenty].reserved = false;
          currentx = x+i;
          currenty = y+j;
          tags[currentx].row[currenty].reserved = true;
          j = j + 1;
      :: (j < 2 && 
            !(x + i < MAX_X 
            && y + j < MAX_Y 
            && x + i >= 0 
            && y + j >= 0 
            && tags[x+i].row[y+j].occupied == false
            && tags[x+i].row[y+j].reserved == false
            && tags[x+i].row[y+j].soilinglevel < tags[currentx].row[currenty].soilinglevel))->
          j = j + 1;
      ::(j >= 2) ->break;
      od;
      j = 0; 
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
    byte i;
    byte j;

    mtype status = SELECT;
    tags[x].row[y].occupied = true;

    x = 0;
    y = 0;
    do
    ::(timer > MAX_TIME) -> break;
    ::(timer <= MAX_TIME && timer > globaltime) ->
        atomic{
          sync(timer)
        }
    ::(timer <= MAX_TIME && timer <= globaltime) ->
        if
        :: (status == MOVE) ->
          atomic{
            timer = timer + MOVE_DELAY;
            tags[x].row[y].occupied = false;
            x = currentx;
            y = currenty;
            tags[x].row[y].occupied = true;
            tags[currentx].row[currenty].reserved = false;
            tags[x].row[y].occupiedby = _pid;
            status = SELECT;
            sync(timer);
          }
        :: (status == CLEAN) ->
          atomic{
            timer = timer + CLEAN_DELAY;
            tags[x].row[y].soilinglevel = timer;
            status = SELECT;
            sync(timer);
          }
        ::(status == SELECT) -> 
          atomic{
            currentx = x;
            currenty = y;
            select_tag(x,y);
          }
          if
            :: (currentx == x && currenty == y) ->
                status = CLEAN;
            :: else -> 
                status = MOVE;
          fi;
        fi

od;

end_ok: false

}

proctype monitor()
{
  int localtime;
        do
        :: d_step { globaltime < MAX_TIME -> 
            localtime = globaltime;
            assert(localtime - tags[0].row[0].soilinglevel <= SOIL_MAX
            && localtime - tags[0].row[1].soilinglevel <= SOIL_MAX
            && localtime - tags[0].row[2].soilinglevel <= SOIL_MAX
            && localtime - tags[0].row[3].soilinglevel <= SOIL_MAX
            && localtime - tags[1].row[0].soilinglevel <= SOIL_MAX
            && localtime - tags[1].row[1].soilinglevel <= SOIL_MAX
            && localtime - tags[1].row[2].soilinglevel <= SOIL_MAX
            && localtime - tags[1].row[3].soilinglevel <= SOIL_MAX
            && localtime - tags[2].row[0].soilinglevel <= SOIL_MAX
            && localtime - tags[2].row[1].soilinglevel <= SOIL_MAX
            && localtime - tags[2].row[2].soilinglevel <= SOIL_MAX
            && localtime - tags[2].row[3].soilinglevel <= SOIL_MAX
            && localtime - tags[3].row[0].soilinglevel <= SOIL_MAX
            && localtime - tags[3].row[1].soilinglevel <= SOIL_MAX
            && localtime - tags[3].row[2].soilinglevel <= SOIL_MAX
            && localtime - tags[3].row[3].soilinglevel <= SOIL_MAX
            ) }
        :: else
        od;
}

init{
  atomic{
    run agent();
    run agent();
    run agent();
    run monitor();
  }
}
