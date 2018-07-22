note
 description : "Elevator application root class"
 date        : "$Date$"
 revision    : "$Revision$"

class
 APPLICATION

create
 make

feature {NONE} -- Initialization

 make
  do

   print("%N_________Test completed___________%N");
  end

  test
  	note
  		explicit: wrapping
  	local
  		e: ELEVATOR
  		max,min,curr: INTEGER
  	do
  		max := 10
  		min:= 0
  		curr:=0
  		create e.make(max, min, curr)
  		check first: not e.doorOpen end
  		e.moveup()
  		check e.currentfloor = 1 end
  		e.movedown()
  		check e.currentfloor = 0 end
  		e.cabbtn (1)
  		e.moveup()
  		e.open()
  		check e.doorOpen end
  		e.close()
  		e.cabbtn (5)
  		e.moveto (5)
  		check e.currentfloor = 5 end
  	end


end
