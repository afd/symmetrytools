#define signal 0

mtype = {ON, OFF, IDLEHIGH, THROTTLEHIGH, TURBOHIGH, LIMITING, OK};
chan cranking_activate = [0] of {bit};
chan idle_activate = [0] of {bit};
chan turbo_activate = [0] of {bit};
chan throttle_activate = [0] of {bit};
chan timing_activate = [0] of {bit};
chan cranking_deactivate = [0] of {bit};
chan idle_deactivate = [0] of {bit};
chan turbo_deactivate = [0] of {bit};
chan throttle_deactivate = [0] of {bit};
chan timing_deactivate = [0] of {bit};
chan idle_initialize = [0] of {bit};
chan fuel_reporter_on = [0] of {bit};

chan report_fuel = [0] of {mtype};
chan report_idle_fuel = [0] of {bit};
chan report_throttle_fuel = [0] of {bit};
chan report_turbo_fuel = [0] of {bit};
chan report_gov_fuel = [0] of {bit};
chan report_cranking_fuel = [0] of {bit};
chan engine = [0] of {mtype};
chan read_tach = [0] of {bit};
chan resp_tach = [0] of {int};
chan done_initializing = [0] of {bit};

active proctype engine_cranking()
{
  end_cranking_control:
  do
  :: cranking_activate?_;
     do
     :: report_cranking_fuel!signal
     :: cranking_deactivate?_ -> break
     od
  od
}

active proctype idle_speed()
{
  end_idle_control:
  do
  :: idle_activate?_;
     do
     :: report_idle_fuel!signal
     :: idle_deactivate?_ -> break
     od
  :: idle_initialize?_
  od
}

active proctype turbocharger()
{
  end_turbo_control:
  do
  :: turbo_activate?_;
     do
     :: report_turbo_fuel!signal
     :: turbo_deactivate?_ -> break
     od
  od
}

active proctype governor()
{
  end_governor:
  do
  :: engine?ON;
     do
     :: if
        :: report_gov_fuel!OK
        :: report_gov_fuel!LIMITING
        fi
     :: engine?OFF -> break
     od
  od
}

active proctype throttle()
{
  end_throttle_control:
  do
  :: throttle_activate?_;
     do
     :: report_throttle_fuel!signal
     :: throttle_deactivate?_ -> break
     od
  od
}

active proctype timing()
{
  end_timing_control:
  do
  :: timing_activate?_;
     timing_deactivate?_
  od
}

active proctype start_car()
{
  end_start_car:
  do
  :: engine!ON
  od
}

active proctype tachometer()
{
  end_tachometer:
  do
  :: read_tach?_;
     if
     :: resp_tach!100
     :: resp_tach!400
     :: resp_tach!60000
     fi
  od
}

active proctype fuelreporter()
{
  end_starting:
  starting:
  fuel_reporter_on?_ -> goto idling;

  end_idling:
  idling:
  if
  :: report_idle_fuel?_; report_throttle_fuel?_;
     if
     :: report_fuel!IDLEHIGH -> goto idling
     :: report_fuel!THROTTLEHIGH -> goto running
     fi
  :: report_throttle_fuel?_; report_idle_fuel?_;
     if
     :: report_fuel!IDLEHIGH -> goto idling
     :: report_fuel!THROTTLEHIGH -> goto running
     fi
  fi;

  end_running:
  running:
  if
  :: report_gov_fuel?LIMITING -> goto running_governed
  :: report_gov_fuel?OK;
     if
     :: report_idle_fuel?_; report_throttle_fuel?_; report_turbo_fuel?_;
        if
        :: report_fuel!IDLEHIGH -> goto idling
        :: report_fuel!THROTTLEHIGH -> goto running
        :: report_fuel!TURBOHIGH -> goto turbocharging
        fi
     :: report_idle_fuel?_; report_turbo_fuel?_; report_throttle_fuel?_;
        if
        :: report_fuel!IDLEHIGH -> goto idling
        :: report_fuel!THROTTLEHIGH -> goto running
        :: report_fuel!TURBOHIGH -> goto turbocharging
        fi
     :: report_throttle_fuel?_; report_idle_fuel?_; report_turbo_fuel?_;
        if
        :: report_fuel!IDLEHIGH -> goto idling
        :: report_fuel!THROTTLEHIGH -> goto running
        :: report_fuel!TURBOHIGH -> goto turbocharging
        fi
     :: report_throttle_fuel?_; report_turbo_fuel?_; report_idle_fuel?_;
        if
        :: report_fuel!IDLEHIGH -> goto idling
        :: report_fuel!THROTTLEHIGH -> goto running
        :: report_fuel!TURBOHIGH -> goto turbocharging
        fi
     :: report_turbo_fuel?_; report_idle_fuel?_; report_throttle_fuel?_;
        if
        :: report_fuel!IDLEHIGH -> goto idling
        :: report_fuel!THROTTLEHIGH -> goto running
        :: report_fuel!TURBOHIGH -> goto turbocharging
        fi
     :: report_turbo_fuel?_; report_throttle_fuel?_; report_idle_fuel?_;
        if
        :: report_fuel!IDLEHIGH -> goto idling
        :: report_fuel!THROTTLEHIGH -> goto running
        :: report_fuel!TURBOHIGH -> goto turbocharging
        fi
     fi
  fi;

  end_turbocharging:
  turbocharging:
  if
  :: report_gov_fuel?LIMITING -> goto turbo_governed
  :: report_gov_fuel?OK;
     if
     :: report_turbo_fuel?_; report_throttle_fuel?_;
        if
        :: report_fuel!THROTTLEHIGH -> goto running
        :: report_fuel!TURBOHIGH -> goto turbocharging
        fi
     :: report_throttle_fuel?_; report_turbo_fuel?_;
        if
        :: report_fuel!THROTTLEHIGH -> goto running
        :: report_fuel!TURBOHIGH -> goto turbocharging
        fi
     fi
  fi;

  end_running_governed:
  running_governed:
  if
  :: report_gov_fuel?OK -> goto running
  :: report_gov_fuel?LIMITING;
     if
     :: report_throttle_fuel?_; report_turbo_fuel?_;
        if
        :: report_fuel!THROTTLEHIGH -> goto running_governed
        :: report_fuel!TURBOHIGH -> goto turbo_governed
        fi
     :: report_gov_fuel?LIMITING; report_turbo_fuel?_; report_throttle_fuel?_;
        if
        :: report_fuel!THROTTLEHIGH -> goto running_governed
        :: report_fuel!TURBOHIGH -> goto turbo_governed
        fi
     fi
  fi;

  end_turbo_governed:
  turbo_governed:
  if
  :: report_gov_fuel?OK -> goto turbocharging
  :: report_gov_fuel?LIMITING;
     if
     :: report_throttle_fuel?_; report_turbo_fuel?_;
        if
        :: report_fuel!THROTTLEHIGH -> goto running_governed
        :: report_fuel!TURBOHIGH -> goto turbo_governed
        fi
     :: report_gov_fuel?LIMITING; report_turbo_fuel?_; report_throttle_fuel?_;
        if
        :: report_fuel!THROTTLEHIGH -> goto running_governed
        :: report_fuel!TURBOHIGH -> goto turbo_governed
        fi
     fi
  fi
}

active proctype controller()
{
  end_car_off:
  car_off:
  if
  :: engine?ON -> goto initializing
  :: engine?OFF -> turbo_deactivate!signal; idle_deactivate!signal;
     throttle_deactivate!signal; timing_deactivate!signal -> goto car_off
  fi;

  end_initializing:
  initializing:
  if
  :: cranking_activate!signal ->
     timing_activate!signal -> goto cranking
  :: engine?OFF -> turbo_deactivate!signal; idle_deactivate!signal;
     throttle_deactivate!signal; timing_deactivate!signal -> goto car_off
  fi;

  end_cranking:
  cranking:
  if
  :: read_tach!signal;
     if
     :: resp_tach?100 -> goto cranking
     :: resp_tach?400 -> cranking_deactivate!signal;
        fuel_reporter_on!signal;
        throttle_activate!signal; idle_initialize!signal;
        idle_activate!signal; turbo_activate!signal -> goto idling
     :: resp_tach?60000 -> goto cranking
     fi
  :: engine?OFF -> turbo_deactivate!signal; idle_deactivate!signal;
     throttle_deactivate!signal; timing_deactivate!signal -> goto car_off
  fi;

  end_idling:
  idling:
  if
  :: report_fuel?IDLEHIGH -> goto idling
  :: report_fuel?THROTTLEHIGH -> goto running
  :: engine?OFF -> turbo_deactivate!signal; idle_deactivate!signal;
     throttle_deactivate!signal; timing_deactivate!signal -> goto car_off
  fi;

  end_running:
  running:
  if
  :: report_gov_fuel?LIMITING -> goto running_governed
  :: report_gov_fuel?OK;
     if
     :: report_fuel?THROTTLEHIGH -> goto running
     :: report_fuel?IDLEHIGH -> goto idling
     :: report_fuel?TURBOHIGH -> goto turbocharging
     fi
  :: engine?OFF -> turbo_deactivate!signal; idle_deactivate!signal;
     throttle_deactivate!signal; timing_deactivate!signal -> goto car_off
  fi;

  end_turbocharging:
  turbocharging:
  if
  :: report_gov_fuel?LIMITING -> goto turbo_governed
  :: report_gov_fuel?OK;
     if
     :: report_fuel?THROTTLEHIGH -> goto running
     :: report_fuel?TURBOHIGH -> goto turbocharging
     fi
  :: engine?OFF -> turbo_deactivate!signal; idle_deactivate!signal;
     throttle_deactivate!signal; timing_deactivate!signal -> goto car_off
  fi;

  end_running_governed:
  running_governed:
  if
  :: report_gov_fuel?OK -> goto running
  :: report_gov_fuel?LIMITING;
     if
     :: report_fuel?TURBOHIGH -> goto turbo_governed
     :: report_fuel?THROTTLEHIGH -> goto running_governed
     fi
  :: engine?OFF -> turbo_deactivate!signal; idle_deactivate!signal;
     throttle_deactivate!signal; timing_deactivate!signal -> goto car_off
  fi;

  end_turbo_governed:
  turbo_governed:
  if
  :: report_gov_fuel?OK -> goto turbocharging
  :: report_gov_fuel?LIMITING;
     if
     :: report_fuel?THROTTLEHIGH -> goto running_governed
     :: report_fuel?TURBOHIGH -> goto turbo_governed
     fi
  :: engine?OFF -> turbo_deactivate!signal; idle_deactivate!signal;
     throttle_deactivate!signal; timing_deactivate!signal -> goto car_off
  fi
}

