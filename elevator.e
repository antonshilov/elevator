note
	description: "Summary description for {ELEVATOR}."
	author: "Anton Shilov"
	date: "21 July"
	revision: "1"
		-- visible fields
	model: doorOpen, maxFloor, minFloor, currentFloor, movUp, movDn, cabBtns, floorUpBtns, floorDnBtns

class
	ELEVATOR

create
	make

feature {NONE} -- Initialization

	make (amaxFl, aminFl, acurrentFl: INTEGER)
			-- Initialization for `Current'.

		note
			status: creator
		require
			amaxFl > aminFl
			amaxFl >= acurrentFl and acurrentFl >= aminFl
			aminFl >=0
		do
			maxFloor := amaxFl
			minFloor := aminFl
			currentFloor := acurrentFl
			doorOpen := FALSE
			movUp := FALSE
			movDn := FALSE

		ensure
			maxFloor = amaxFl
			minFloor = aminFl
			currentFloor = acurrentFl
			doorOpen = FALSE
			movUp = FALSE
			movDn = FALSE
		end


feature -- Access

	doorOpen, movUp, movDn: BOOLEAN;

	maxFloor, 	minFloor, 	currentFloor: INTEGER;
	cabBtns, floorUpBtns, floorDnBtns: MML_SET[INTEGER];

feature -- Methods
	moveUp()
		require
			modify_model("currentfloor",Current)
			currentFloor < maxFloor
			not doorOpen
		do
			currentFloor:= currentFloor+1
		ensure
			currentFloor = old currentFloor+1
		end

	moveDown()
		require
			modify_model(["currentfloor"], Current)
			validFl:	currentFloor > minFloor
			closed: not doorOpen
		do
			currentFloor:= currentFloor-1
		ensure
			moved: currentFloor = old currentFloor-1
		end
	setMovUp(state: BOOLEAN)
		require
			modify_model("movup",Current)
			not movDn
			state implies not doorOpen
		do
			movUp:=state
		ensure
			movUp=state
			movUp implies not doorOpen
		end
	setMovDn(state: BOOLEAN)
		require
			modify_model("movdn",Current)
			not movUp
			state implies not doorOpen
		do
			movDn:=state
		ensure
			movDn=state
			movDn implies not doorOpen
		end

	cabBtn(fl: INTEGER)
		require
			modify_model(["cabbtns"], Current)
			validFl:	fl >= minFloor and fl<=maxFloor and not (fl = currentFloor)
		do
			cabBtns:= cabBtns & fl
		ensure
			cabBtns = old cabBtns & fl
		end

	pushUp(fl: INTEGER)
		require
			modify_model(["floorupbtns"], Current)
			validFl:	fl >= minFloor and fl<=maxFloor and not (fl = currentFloor)
		do
			floorUpBtns:= floorUpBtns & fl
		ensure
			floorUpBtns = old floorUpBtns & fl
		end
	pushDn(fl: INTEGER)
		require
			modify_model(["floordnbtns"], Current)
			validFl:	fl >= minFloor and fl<=maxFloor and not (fl = currentFloor)
		do
			floorDnBtns:= floorDnBtns & fl
		ensure
			floorDnBtns = old floorDnBtns & fl
		end
	open()
		require
			modify_model(["dooropen","cabbtns", "floorupbtns", "floordnbtns"], Current)
			validMove: not movUp and not movDn
			reachedDest: cabBtns[currentFloor] or floorUpBtns[currentFloor] or floorDnBtns[currentFloor]
			doorClosed:	not doorOpen
		do
			cabBtns:= cabBtns / currentFloor
			floorUpBtns:= floorUpBtns / currentFloor
			floorDnBtns:= floorDnBtns / currentFloor
			doorOpen:= TRUE
		ensure
			cabBtns = old cabBtns / currentFloor
			floorUpBtns = old floorUpBtns / currentFloor
			floorDnBtns = old floorDnBtns / currentFloor
			doorOpen
		end
	close()
		require
			modify_model(["dooropen"], Current)
			validMove: not (movUp or movDn)
			doorOpen
		do
			doorOpen:= FALSE
		ensure
			not doorOpen
		end

	moveTo(fl: INTEGER)
		note
			explicit: wrapping
		require
			modify_model(["movup", "movdn","currentfloor","dooropen", "cabbtns", "floorupbtns", "floordnbtns"], Current)
			validMove: not (movUp or movDn)
			validDest: not (currentFloor = fl) and (fl >= minFloor) and (fl <= maxFloor)
			validFlBtns: floorUpBtns.max <= maxFloor and floorUpBtns.min >= minFloor
			validFlDnBtns: floorDnBtns.max <= maxFloor and floorDnBtns.min >= minFloor
			validCabBtns: cabBtns.max <= maxFloor and cabBtns.min >= minFloor
			hasDest: cabBtns[fl]
			doorClosed: not doorOpen
		do
			if currentFloor > fl then
				setMovDn(TRUE)
				moveToDn(fl)
				setMovDn(FALSE)
			else
				setMovUp(TRUE)
				moveToUp(fl)
				setMovUp(FALSE)
			end
			open()
			close()
		ensure
			removedDest: cabBtns = old cabBtns / currentFloor
			reachedDest: currentFloor = fl
			notMoving: not (movUp and movDn)
			doorClosed:not doorOpen
		end

	moveToDn(fl: INTEGER)
		note
			explicit: wrapping
		require
			modify_model(["currentfloor", "dooropen", "movdn", "floordnbtns"], Current)
			validMove: movDn
			validDest: not (currentFloor = fl) and (fl >= minFloor) and (fl <= maxFloor) and (currentFloor > fl)
			hasDest: cabBtns[fl]
			validFlDnBtns: floorDnBtns.max <= maxFloor and floorDnBtns.min >= minFloor
			doorClosed: not doorOpen
		do
			from

			invariant
				dest_less_current: fl<= currentFloor
				doorClosed: not doorOpen
			until
				currentFloor = fl
			loop
				moveDown()
				if (floorDnBtns.has(currentFloor)) then
					setMovDn(FALSE)
					open()
					close()
					setMovDn(TRUE)
				end
			variant
				currentFloor - fl
			end
		ensure
			currentFloor = fl
			reachedDest: cabBtns[currentFloor]
			not doorOpen
		end

	moveToUp(fl: INTEGER)
		note
			explicit: wrapping
		require
			modify_model(["currentfloor", "dooropen", "movup", "floorupbtns"], Current)
			validMove: movUp
			validDest: not (currentFloor = fl) and (fl >= minFloor) and (fl <= maxFloor) and (currentFloor < fl)
			hasDest: cabBtns[fl]
			validFlBtns: floorUpBtns.max <= maxFloor and floorUpBtns.min >= minFloor
			doorClosed: not doorOpen
		do
			from

			invariant
				dest_more_current: fl >= currentFloor
				doorClosed: not doorOpen
			until
				currentFloor = fl
			loop
				moveUp()
				if (floorUpBtns.has(currentFloor)) then
					setMovUp(FALSE)
					open()
					close()
					setMovUp(TRUE)
				end
			variant
				fl - currentFloor
			end
		ensure
			currentFloor = fl
			reachedDest: cabBtns[currentFloor]
			not doorOpen
		end

feature -- Status report

feature -- Status setting

feature -- Cursor movement

feature -- Element change

feature -- Removal

feature -- Resizing

feature -- Transformation

feature -- Conversion

feature -- Duplication

feature -- Miscellaneous

feature -- Basic operations

feature -- Obsolete

feature -- Inapplicable

feature {NONE} -- Implementation

invariant
	invariant_clause: True -- Your invariant here
	maxFloor > minFloor
	maxFloor >= currentFloor and currentFloor >= minFloor
	minFloor >=0
	notUpIfDn: movUp implies not movDn
	notDnIfUp: movDn implies not movUp
	closedWhenMoving: movUp or movDn implies not doorOpen
end
