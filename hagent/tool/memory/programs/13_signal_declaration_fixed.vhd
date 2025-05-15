library IEEE;
use IEEE.STD_LOGIC_1164.ALL;

entity Inverter is
  Port ( input : in  STD_LOGIC;
         output : out STD_LOGIC);
end Inverter;

architecture Behavioral of Inverter is
  -- Fixed: Added semicolon after signal declaration
  signal intermediate : STD_LOGIC;
begin
  intermediate <= not input;
  output <= intermediate;
end Behavioral; 