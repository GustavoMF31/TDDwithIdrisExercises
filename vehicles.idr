%default total

-- Let's try to replicate the dependent example with simple algebraic data types
data PetrolVehicle = Car' Nat | Bus' Nat
data PedalVehicle = Bike'
data Vehicle' = Petrol' PetrolVehicle | Pedal' PedalVehicle

wheels' : Vehicle' -> Nat
wheels' (Petrol' (Car' _)) = 4
wheels' (Petrol' (Bus' _)) = 4
wheels' (Pedal' _) = 2

refuel' : PetrolVehicle -> PetrolVehicle
refuel' (Car' k) = Car' 100
refuel' (Bus' k) = Bus' 200

data Power = Petrol | Pedal | Electric
data Vehicle : Power -> Type where
  Bycicle : Vehicle Pedal
  Car : (fuel : Nat) -> Vehicle Petrol
  Bus : (fuel : Nat) -> Vehicle Petrol
  -- Extra
  Unicycle : Vehicle Pedal
  Motorcycle : (fuel : Nat) -> Vehicle Petrol
  ElectricCar : (energy : Nat) -> Vehicle Electric

wheels : Vehicle _ -> Nat
wheels Bycicle = 2
wheels (Car fuel) = 4
wheels (Bus fuel) = 4
wheels Unicycle = 1
wheels (Motorcycle fuel) = 2
wheels (ElectricCar energy) = 4

refuel : Vehicle Petrol -> Vehicle Petrol
refuel (Car fuel) = Car 100
refuel (Bus fuel) = Bus 200
refuel (Motorcycle fuel) = Motorcycle 50


