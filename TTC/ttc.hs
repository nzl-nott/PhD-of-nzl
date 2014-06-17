module TTC where


type Tape = ([Int], Int, [Int])
type Segment = [Int]

-- assuming it is symmetry so only positive numbers

replacement :: [Int]
replacement = [2,5,6]


---- printing length
print_length_l :: Int
print_length_l = 5
print_length_r :: Int
print_length_r = 20

empty :: [Int]
empty = 0 : empty

empty_fin :: Int -> [Int]
empty_fin n = take n (repeat 0)

start :: Tape
start = (empty,1,empty)


cut :: (Int,Int) -> Tape -> Segment
cut (x,y) (l,c,r) | x > y           = error "wrong input"
                  | x < 0 && y < 0  = reverse (drop (-y+1) (take (-x) l))
                  | x < 0 && y == 0 = reverse (c : take (-x) l)
                  | x < 0 && y > 0  = reverse (take (-x) l) ++ c : (take y r)
                  | x == 0 && y >= 0 = c : (take y r)
                  | x > 0  && y > 0  = drop (x-1) (take y r)
                  | otherwise        = error "wrong input"


				  
printS :: Segment -> String
printS [] = " |"
printS (x:xs) | x < 0 = " | " ++ show x ++ printS xs
              | otherwise = " |  " ++ show x ++ printS xs

printBar :: (Int,Int) -> String
printBar (x,y) | x < y && x >=0 && x <=9 = " |  " ++ show x ++ printBar (x+1,y)
               | x < y  = " | " ++ show x ++ printBar (x+1,y)
			   | x == y && x >=0 && x<=9 = " |  " ++ show x ++ " | "
               | x == y = " | " ++ show x ++ " | "
			   | otherwise = error "wrong input"

print_line :: String
print_line = take (12 + 5 * (print_length_l+print_length_r)) (repeat '-') ++ "\n"
			   
printT :: (Int,Int) -> Tape -> IO ()
printT (x, y) t = putStr ("..." ++ printBar (x,y) ++ "..."++ "\n" ++ print_line ++ "..." ++ printS (cut (x,y) t) ++ "..." ++ "\n" ++ print_line++"\n")


data Command = E | C



-- assuming sorting list

m1 :: Int -> Int
m1 n = n-1

add_coins :: [Int] -> [Int] -> [Int]
add_coins [] ys = ys
add_coins (x:xs) (y:ys) | x == 1    = (y+1) : add_coins (map m1 xs) ys
                        | otherwise = y : add_coins (map m1 (x:xs)) ys

-- modes

data Mode = Safe | Unsafe
						
take_coin :: Mode -> Int -> Int
take_coin Unsafe n            = n-1		
take_coin Safe n  | n <= 0    = error "impossible move"
                  | otherwise = n-1
		 
		 
take_coins :: Mode -> [Int] -> [Int] -> [Int]
take_coins m [] ys = ys
take_coins m (x:xs) (y:ys) | x == 1    = take_coin m y : take_coins m (map m1 xs) ys
                           | otherwise = y : take_coins m (map m1 (x:xs)) ys

exec_aux :: Mode -> Command -> Tape -> Tape
exec_aux m E (l,c,r) = (add_coins replacement l ,take_coin m c, add_coins replacement r)
exec_aux m C (l,c,r) = (take_coins m replacement l, c+1       , take_coins m replacement r)

move :: Int -> Tape -> Tape
move n (l,c,r) | n==0 = (l,c,r)
               | n<0  = move (n+1) (tail l, head l, c:r)
               | n>0  = move (n-1) (c:l, head r, tail r)		   

exec :: Mode -> Command -> Int -> Tape -> Tape
exec m c n t = move (-n) (exec_aux m c (move n t))

exec_io :: Mode -> (Command,Int) -> Tape -> IO Tape
exec_io m (c,n) t = return (exec m c n t)

run :: Mode -> [(Command,Int)] -> Tape -> IO()
run m [] t = putStr "End\n"
run m ((c,n):xs) t = do printT (-print_length_l,print_length_r) new_tape
                        run m xs new_tape
                     where
                       new_tape = exec m c n t
					 
process :: String -> (Command,Int)
process (c:s) | c == 'e' || c == 'E' = (E,p)
              | c == 'c' || c == 'C' = (C,p) 	
                                       where
                                         p = read s :: Int
process _                            = error "wrong input"										 
					
part :: Mode -> Tape -> IO()
part m t = do putStr "Enter command:"
              command <- getLine
              new_tape <- exec_io m (process command) t
              printT (-print_length_l,print_length_r) new_tape
              part m new_tape

char2mode :: Char -> Mode
char2mode 'S' = Safe
char2mode 's' = Safe
char2mode 'U' = Unsafe
char2mode 'u' = Unsafe
char2mode _   = error "reprompt is better!"

main :: IO()
main = do printT (-print_length_l,print_length_r) start
          putStr "Enter mode(safe(s)/unsafe(u)):"
          m <- getLine
          part (char2mode (head m)) start