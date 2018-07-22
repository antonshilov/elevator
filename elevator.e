note
	description: "Summary description for {ELEVATOR}."
	author: "Anton Shilov"
	date: "21 July"
	revision: "1"
		-- visible fields
	model: doorOpen, maxFloor, minFloor, currentFloor, movUp, movDn, cabBtns

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
	cabBtns: MML_SET[INTEGER];

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
			not doorOpen
		do
			currentFloor:= currentFloor-1
		ensure
			currentFloor = old currentFloor-1
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
	open()
		require
			modify_model(["dooropen","cabbtns"], Current)
			validMove: not (movUp or movDn)
			reachedDest: cabBtns[currentFloor]
			not doorOpen
		do
			cabBtns:= cabBtns / currentFloor
			doorOpen:= TRUE
		ensure
			cabBtns = old cabBtns / currentFloor
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
		require
			modify_model(["movup", "movdn","currentfloor","dooropen", "cabbtns"], Current)
			validMove: not (movUp or movDn)
			validDest: not (currentFloor = fl) and (fl >= minFloor) and (fl <= maxFloor)
			hasDest: cabBtns[fl]
			doorClosed: not doorOpen
		do
			if currentFloor > fl then
				movDn:=TRUE
				moveToDn(fl)
				movDn:=FALSE
			else
				movUp:=TRUE
				moveToUp(fl)
				movUp:=FALSE
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
		require
			modify_model(["currentfloor"], Current)
			validMove: movDn
			validDest: not (currentFloor = fl) and (fl >= minFloor) and (fl <= maxFloor) and (currentFloor > fl)
			hasDest: cabBtns[fl]
			doorClosed: not doorOpen
		do
			from

			invariant
				dest_less_current: fl<= currentFloor
			until
				currentFloor = fl
			loop
				moveDown()
			variant
				currentFloor - fl
			end
		ensure
			currentFloor = fl
			reachedDest: cabBtns[currentFloor]
		end

	moveToUp(fl: INTEGER)
		require
			modify_model(["currentfloor"], Current)
			validMove: movUp
			validDest: not (currentFloor = fl) and (fl >= minFloor) and (fl <= maxFloor) and (currentFloor < fl)
			hasDest: cabBtns[fl]
			doorClosed: not doorOpen
		do
			from

			invariant
				dest_more_current: fl >= currentFloor
			until
				currentFloor = fl
			loop
				moveUp()
			variant
				fl - currentFloor
			end
		ensure
			currentFloor = fl
			reachedDest: cabBtns[currentFloor]
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
	movUp implies not movDn
	movDn implies not movUp
	movUp or movDn implies not doorOpen
end
