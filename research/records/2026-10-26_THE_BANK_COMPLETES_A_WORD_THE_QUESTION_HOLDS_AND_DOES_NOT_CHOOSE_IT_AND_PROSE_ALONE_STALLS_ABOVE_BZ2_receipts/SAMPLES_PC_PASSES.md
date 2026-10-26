# The PC's reports on the amended bank's passes 4 to 7

The reports Brandon's PC sent after each pass, as sent, with the message channel's `&lt;`, `&gt;` and `&amp;` escapes undone, so every sample is the bytes the tower released. One line naming the run directory is cut from the last report. The run directory and its binaries are not in the repository.

---

## Report: pass4

PC run, pass 4 of 4 (amended key, bank-john worktree at 29b76d727 detached; the main checkout is untouched; nothing committed)

Reading: no sample answers about John. As written, 0 of 16 bankA4 samples name John. Framed, 1 of 16 names him: key stream 6, two draws, where after "#### 1" a new question opens "John has already has already…" and loops; it is not the volunteer question. No sample anywhere contains "volunteer", "shelter" or 72. The foil4 samples on the prompt as written name John in 0 of 16. Held-out: bankA4 1.610 bits a byte, beside 1.607 for the old-key bank4 and 1.822 for foil4.

Setup receipts:
- Build: 126.5 s.
- `cargo test --release -p holonics --lib hnn::tower::bank` selects 0 tests, because bank.rs has no test module. The eleven are the tests the filter `bank` selects: 11 passed, 0 failed.
- Join: `TOWER_BANK_JOINED bank 0 64 8 8 material=290604`; bankA.state sha256 fa18c487279e14b5d0d0746dbd3496535ce1117ca18b6cb00e7abdcce2098dfa.
- prompt_framed.txt: e697eca0…9652, as required. train300.txt: 162,937 bytes, 15b1aac8f8376361…, as required.
- Timing read on train300 (60 sections), banked and foil together, 8 threads each:
  - banked: windows 153.9 and 145.5 ms a section, held-out read 4.48 s, wall 13.6 s, peak 347,468 KiB, `TOWER_PASS train 1.799 dev 1.819 Q=1.960 P=1.643 N=2.502 M=1.357`;
  - foil: windows 74.3 and 73.8 ms a section, read 3.0 s, wall 7.6 s, peak 196,872 KiB.
- foil4 resampled on the new binary: all 16 samples are byte-identical to the old binary's, so the bankless path is unchanged.
- /usr/bin/time is not installed on this host. Every receipt is the run's wait4 rusage (wall time and peak resident set).
- bankA5 and foil5 are running now. Their projections are 206.2 s (deadline 207 s) and 107.2 s (deadline 108 s).

## Pass 4: amended key (29b76d727), banked bankA4, bankless foil foil4

**bankA4**: PROJECTION 1311 x 153.9 ms + 4.48 s = 206.2 s (153.9 ms: the largest 32-section window of devK_bank, the amended key's only timing read, run beside devK_foil; 4.48 s its held-out read); DEADLINE 207 s (runner timer and outer timeout); early stop when the mean section time passes 153.9 ms; RAYON_NUM_THREADS=8, alone (foil4 already trained)
measured: wall 165.2 s (0.80 of the projection), peak resident set 383244 KiB; `RUN_RECEIPT exit=0 wall_s=165.2 peak_rss_kib=383244 user_s=1150.6 stopped=no`; windows 119.8–143.7 ms, mean 122.3
`TOWER_PASS pass=0 train_bits_a_byte=1.629 dev_bits_a_byte=1.610 dev_regions Q=1.820 P=1.350 N=2.299 M=1.186 deposits=1311/1311 pass_ms=164775 elapsed_ms=164804`
state bankA4/STATE sha256 5f9f9eeed0b3008e28b35ddfefe2317eb10bb8c8c1dc8187d732ea00355c414c

**foil4** (the earlier run here, unchanged): PROJECTION 1311 x 77.4 ms + 3.15 s = 104.6 s; DEADLINE 105 s; beside bank4
measured: wall 104.2 s, peak resident set 209948 KiB; `RUN_RECEIPT exit=0 wall_s=104.2 peak_rss_kib=209948 user_s=610.2 stopped=no`
`TOWER_PASS pass=0 train_bits_a_byte=1.787 dev_bits_a_byte=1.822 dev_regions Q=1.909 P=1.708 N=2.511 M=1.351 deposits=1311/1311 pass_ms=103680 elapsed_ms=103712`
state foil4/STATE sha256 847788e3f97d646b2d68e1b37999e37bc1c770004133fa5ef69a9ba877836c72

### bankA4, prompt as written: 0 of 16 samples name John

bankA4 as written, key stream 1, one draw (401 bytes, prompt 2.224 bits a byte; "John" 0x)
```text
What they half few compasking both sides to find the cost $8=$<<24/2=5>>5/2=3>>3T
30*x+0*.10 = <<15*.10=90>>90 inructs
#### 80

The first store.  Five uch money did on 5% bille at to read, and Kate's watermine a pmallest. On the same of their friend is emus a three gift videos?
Texter wants to decide the pangords at 100% of 1 tiams. If alf Lurant had 40C company a, how much alf does Tim made twice 
```

bankA4 as written, key stream 1, two agreeing draws (401 bytes, prompt 2.224 bits a byte; "John" 0x)
```text
The rest of the went scored in the first this week so that's 2*2=<<2*2=4>>4 hours.
The total number of stocks Bendy is 6 + 6 = <<6+6+6=14>>14 weeks.
#### 49

Jimum has 20 people went a month and one-third section. The number of still has 20 sections. On Sunday he is olded to the flight is 3 of their squirts are game for his tead and each squirts for a section. The casses are for the flight is 5 day
```

bankA4 as written, key stream 2, one draw (402 bytes, prompt 2.224 bits a byte; "John" 0x)
```text
Each of Dar sock has × Y = <<2*3=6>>6 aws.
Sinc the same arre bought 3 times did, Rix is 3 * 2*2 = <<3*2=6>>6 students.
So in 2 hours (20-<<300+50=400>>420
They put for $5% of her classes in 5 kilometores uppown 30-5=3
The rucced to 24/hour of canded for 2 hour/mond spends 2*. total = $<<10*0.2=14>>14
Tually, the flight is 20-12=<<60-8=40>>50 miles to the eggs drink  her Sunill.
Tong is 3 * 2 = <<3
```

bankA4 as written, key stream 2, two agreeing draws (400 bytes, prompt 2.224 bits a byte; "John" 0x)
```text
The sent a month is 50 - 8 = <<60-12=60>>60 sent a month is two ent a month is half the pone toaome.
Therefore, Sunday he has 20 - 5 = <<20-20=15>>15 tickets.
The sent a month is 6*2=<<6*2=8>>8.
Thus, Tom plays and he has 6*3 = <<6*3=12>>12 vole moved.
#### 4

The sent a total distance coball has 2 less than Brym and twice as many as the number of sent a month is a pence. If Michael is a pagoa mon
```

bankA4 as written, key stream 3, one draw (401 bytes, prompt 2.224 bits a byte; "John" 0x)
```text
Monday Tim has half a 17:4
He earned 180-4 = <<341-4=66>>66 pound grous in on his homs.
The total weight number she speed enough to sumbrother a retails, and contains five years, we must Maxim to text twice as he gets 36 people / 3 = <<380/3=22>>2 loods
So his cheese 50/15-2 = <<360-18=15>>15 minutes
The weekly pringed 200 grams of sod would be donation in half the first hour so that's 2 - 2 = <<18
```

bankA4 as written, key stream 3, two agreeing draws (402 bytes, prompt 2.224 bits a byte; "John" 0x)
```text
In the second equals <<100*2=500>>500 dollars.
He has a new still for the two days per hour, and he has a home for 6/2 = <<8/2=3>>3 hours.
When he needs to find the time he has a home and the two days per hour, each day?
First, he has a home and he has a home with 120 + 3 = <<80+3=40>>40 minutes.
The bason cird has a home for 30 + 30 + 300 = <<30+300+30+40=150>>150 miles away usice.
#### 60

Tom is 
```

bankA4 as written, key stream 4, one draw (400 bytes, prompt 2.224 bits a byte; "John" 0x)
```text
If Tachie made 8*40 = <<8*60=120>>120 loaz
Then find the difference, there are 5 hours watching the first 00 ming time: 12,0/14=eginn the age sinking time
In the other 5*60=creams 10
Three sath will subtract three year she be Jill has enough to There get 50/3 = 4 days by the weight renoteens
So he sold 7*6 = <<5*6=36>>36
He needs to winner the park the store for 2/3 x 7 = <<2*12=60>>60 cats.
So a 
```

bankA4 as written, key stream 4, two agreeing draws (400 bytes, prompt 2.224 bits a byte; "John" 0x)
```text
The shop, she has 14 * 2 = <<7*2=28>>108
#### 610

A cars is twice as many lots as three times as three times as three times as three times as three times as three times as three times as three times as three times as three times as three times as three times as three times as three times as three times as is four times as three times as three times as three times as three times as three times as 
```

bankA4 as written, key stream 5, one draw (400 bytes, prompt 2.224 bits a byte; "John" 0x)
```text
The work't like t-oz
2 * $10 = <<3*10=8>>8 plives.
So a page t*splan pants + 5 each = <<20+5+8=24>>24 statia
Hen points 1% are sweeded up so takes 2 goals 1/2*3 = 24 feet wid time it.
#### 45

The first Cin ular is over the jet we'sin, who scnumber Kay. So Purther has twice the number of apples car has it takes to Ang to fivnd almons, 4 times the cak?
The first carr's tain-kilos of 25 - 60 = <<60-
```

bankA4 as written, key stream 5, two agreeing draws (402 bytes, prompt 2.224 bits a byte; "John" 0x)
```text
The first floor, 3 hours is 4 * 2 = <<2*300=500>>500 students.
#### 500

Mater's is takes for $3, how much did on his sead Feer's game?
Lake is 40*15 = <<2*100=150>>150 miles per hour.
So he has to get hight is 40*15=$<<2*40=100>>100
He is 40*15=$<<40*15=100>>100
He gets 40*15=$<<50*15=1000>>1000
He gets 40*100=$<<500*15=1000>>1000
He is 40*1000 = $<<20*1000=1000>>1000 people.
Since the rrepress 20 
```

bankA4 as written, key stream 6, one draw (402 bytes, prompt 2.224 bits a byte; "John" 0x)
```text
When sck will drink 3*.5=<<4*.5=9>>9 gamoo
He knows the salas, the two ant feet of 3 off so will be 340 x 6 + 34 = <<25+35+15+5*32=112>>21 hours.
So, thubtracd 60 travels saved 30 equal to contains 10+48 = <<50+30=32>>4200.
#### 352

Toon has 7 Viveling goody in milkfather and 20 people during. The pieces of 45 liters piec. One sist is start 50 liters each.  How much did Jracing wato marbling?
They 
```

bankA4 as written, key stream 6, two agreeing draws (401 bytes, prompt 2.224 bits a byte; "John" 0x)
```text
On the third of 5 days * 10 sple = <<2*10=30>>30 people at the farm.
The next day, she will take 4 * 3 = <<2*3=6>>6 cookies.
#### 6

For the rest of the remaining came amount of ments ducte. She still has 20 more than dogs each of the rack. She also has 20 minutes to add a still and 5 miles through and 5 miles thy. She thy tickst twice as many sets of as his maxim. She still has 20 minutes to ruvol
```

bankA4 as written, key stream 7, one draw (400 bytes, prompt 2.224 bits a byte; "John" 0x)
```text
Each day Michael’ steal is 4*24 = <<12*6=240>>240 years
15+600+6x+400 = 48 pounds bottles of internsill.
Michael currently 30 and Ryris charges by the game, which drinkated on the ounce, 400 + 25% - 2500 + 120 miles = <<200+200+200=150>>150 miles sharing like test to wall the same produced.
#### 30100

Adunha has a pair of all sold third unlostere, and seat two legs wall of the flight a’s stor
```

bankA4 as written, key stream 7, two agreeing draws (401 bytes, prompt 2.224 bits a byte; "John" 0x)
```text
If he has a new company is $250 x 2 = $<<60*2=500>>2500 students in a day.
#### 500

Bill is 500 students. She already has a sheld cost $0.00 as third. The donating watermine got a sheld costs $.5 for the gresheld cost $.5 for the next. The group has a sheld costs $.5 for the game, which cost $.5 for the game. If he has a sheld costs $.5 for the game, how much will she have to rice each and his ruc
```

bankA4 as written, key stream 8, one draw (400 bytes, prompt 2.224 bits a byte; "John" 0x)
```text
There will be 60 + 3 = <<60+3=280>>450 tail
The cost of one before is offering owers a he, the soluns ses 4*2=<<12*2=25>>25 peoplels after selling all the 2>>130 morcks.
That means he is 3 * 8 = <<8*6=2>>2 to the store.
The father now, Evert doubled total ounces of adderming, Ol the same cost 20/.6 = <<10/.6=2>>s
#### 2

Tonian collect 10 yellow old up. He of 500 So, Rual has 2*3=<<3*3=6>>6 apple 
```

bankA4 as written, key stream 8, two agreeing draws (402 bytes, prompt 2.224 bits a byte; "John" 0x)
```text
The school has 5 / 2 = <<60/2=5>>5 miles per hour.
A still has 5 + 2 = <<20+2=8>>8 miles per hour.
#### 6

A still has 12 years old. If he has 5 quarters are there he has 5 litters, how many people are there in a day he has 5 years?
There are 5 times as many hours per hour, 5/2 = <<60/2=30>>30 people in the donater.
#### 15

Michael has 5 years old. If he has 5 years old. The second three times as m
```

### bankA4, prompt framed: 1 of 16 samples name John

bankA4 framed, key stream 1, one draw (401 bytes, prompt 1.936 bits a byte; "John" 0x)
```text
Three less left 3 fewer inches – 2 liters leaves per hour, 1 takes 10 people need a day and 20/100D
60*6+3*.6 = <<7*35=150>>150 students.
He goes edie tree six also ban 4.50/3 = <<2,50-50=40>>40
Combining likes one-third is twice the distance contain 100-25 = <<100-25=100>>100 balls of picity covering tail.
She gets 10 discount of tomm * 60 s= $<<2*60=500>>500 crees.
Her every day, he have to vis
```

bankA4 framed, key stream 1, two agreeing draws (402 bytes, prompt 1.936 bits a byte; "John" 0x)
```text
The rest of the went to the first give and he receives 5 * 3 = <<2*3=6>>6 miles per hour.
The rest of the Calia is 2+2+2=<<2+2=6>>6 miles per hour.
The total number of rolls has 18 - 6 = <<18-8=8>>8 tion rolls
#### 4

A is 4 hours. She makes 4 hours. How many people did she have to see before the ball of the both sides than Jenny spend for 30 minutes than Jenny spend for the cion and he did he have 
```

bankA4 framed, key stream 2, one draw (401 bytes, prompt 1.936 bits a byte; "John" 0x)
```text
Each of Jank was 2/15*5=<<2*25=80>>80 such time.
The tip is 120*500=2/sq.celling.
The price was 1 sax on the school; every .20-third shirt of each company has f 6/hour video got, the school, addition% 50 kg, Sunmallest catch, Sundica's =1/2 of the nennker drink for the lifflo returns working.
#### 200

Tentl on hermine were paid dangole for a half of each of each the school ander pencil.  +20 exerc
```

bankA4 framed, key stream 2, two agreeing draws (402 bytes, prompt 1.936 bits a byte; "John" 0x)
```text
The second, he has 30 / 2 = <<60/2=50>>50 people in the second day.
The second, he has 10 feet less than und, he has 30 + 20 = <<60+20+20=120>>120 minutes left
The seconds a homating the first second, she has 10 feet less than undition, he has 20 + 20 - 40 = <<60-150=60>>60 pounds
#### 20

A company Dony wanted a total of 40 years old. If he has 30 minutes and Brym has 30 minutes in a day, how many 
```

bankA4 framed, key stream 3, one draw (400 bytes, prompt 1.936 bits a byte; "John" 0x)
```text
Christinus and feet ded $3, 10%, they flakes 8 x 4 = <<3*4=6>>6 apples
In total, the It has that the two weeks for a total of 2-3=<<2+4=7>>7 visits
Then subtract the hold next year: 1 stickers + 12 + 12 + 60 sectr = <<15+60+12=90>>90 calorials porting camos.
Josh take 10 dumballs volon gives home for a total of 3+3 = 28.
If it takes 100+60=<<300+60=300>>300 dollars contains 3 days do briced by 3. 
```

bankA4 framed, key stream 3, two agreeing draws (401 bytes, prompt 1.936 bits a byte; "John" 0x)
```text
If the first four feet wne is 50*5 = <<30*5=15>>15 dollars.
So, he has increased, they has 20 + 20 = <<60+20=30>>30 more square feet.
The square feet ward is 50*5 = <<60*5=240>>240 years old.
#### 60

With the third of the square feet want to the third of the square feet want, he cuts wanted up. If each scum dird to raise his dog of his dog of his dog of his dog of his dog of his dog of his dog of 
```

bankA4 framed, key stream 4, one draw (401 bytes, prompt 1.936 bits a byte; "John" 0x)
```text
If a mards two Pwas so Benala Greger then the distance?
Epers left 5 times as much as His men is 100*40 = <<00*60=240>>240 reage destiver tains in the a tablulance.
There will be bating x 5% - 70 so he eats 60 hount daugated a minute and 30 more people in the doubled 12/store = 1800-200 = <<600-100=900>>600 dollars.
#### 4200

A swaract three times old is once and is friends went from each hit dang
```

bankA4 framed, key stream 4, two agreeing draws (400 bytes, prompt 1.936 bits a byte; "John" 0x)
```text
The supplies have a $5 x .25 = $<<5*.5=5.5>>5.5
#### 5.5

A flight is min sales for $5. They had $50 per hour. They has to buy a 25 of the books, how many people went before does he have left after he have left?
The supplies are cakes a necklaces for a total of $50/hour = $<<15*20=35>>35.
The supplies and 5 people and 5 people in a necklaces for a total of $5 people in a necklaces for a total of $
```

bankA4 framed, key stream 5, one draw (401 bytes, prompt 1.936 bits a byte; "John" 0x)
```text
The other eo games $0.5*6 = $500/100 littei father.
So he is 100-$500=80 are theating the box.
Thus, the 24>>24 and each tixes now 1/2.5*2x.150+2 = $<<310+2=100>>100 kgs
We receive the first running: 100 visit 80 equal, X = <<120+12=85>>29:.25-25*500=<<300-25=100>>100.
#### 200

Tony has 250 tan. How many hours does Corximum student is 1/2 buyb, the final water make ador class at the Saturday aroun
```

bankA4 framed, key stream 5, two agreeing draws (400 bytes, prompt 1.936 bits a byte; "John" 0x)
```text
The first fewer peals <<150*3=28>>28 hours a still watch.
The second year, he before is 300*15 = <<120*15=300>>300 cars she bot.
The second year, she baking 200 cars - 160 minutes + 3 cats. Each of flies has 20 + 300 = <<100+300+300+300=500>>500 cars in his dog in his dog and his takes for the baking.
#### 500

Marti has 20 years agre. Tond has 20 years agre. The vegetable is 4 ounces of clothes, 
```

bankA4 framed, key stream 6, one draw (401 bytes, prompt 1.936 bits a byte; "John" 0x)
```text
When tho the remaining in 70% babin o, there are 16 contain 400 so that's 2*25 = 1400 sets each sal squires brew the for the initial computt.
Since Doll cat Junt Rits panted to his friend working one-local half the second sict.
The colper temals, the Tvalan bought is 16-6 = <<80+160=40>>40 sposess Carlay.
#### 25

Amanan's age of excat rangether . The ranhas.
2-8=<<24=18>>18 points
He is means the 
```

bankA4 framed, key stream 6, two agreeing draws (403 bytes, prompt 1.936 bits a byte; "John" 1x)
```text
Since the ball has already is 2-3=<<2+3=6>>6 bananas.
The first this means three times as many people in a sax 3 = <<2/3=3>>3.
#### 1

John has already has already has already has already has already has already has already has already has already has already has already has already has already has already has already has morning. She has already has already has already has amily has already has amil
```

bankA4 framed, key stream 7, one draw (400 bytes, prompt 1.936 bits a byte; "John" 0x)
```text
Each day Royst’s bear days is 4*60 = <<30*60=40>>40 minutes
Yory sat Sonmen a total of $1200 / $2 = $<<200/2=200>>300.
All be the annah and groine that willurrental compound sectiremate a total of $12 + $16 * 2 = $<<6*2=16>>16.
Thus, which is 183 equals <<5*32=240>>240 cups.
Tom, the rest of the engates need to leaf the last crecoals 1 * 2 = $<<5*2=30>>30 standon a fish.
Ho balls March sold is $
```

bankA4 framed, key stream 7, two agreeing draws (403 bytes, prompt 1.936 bits a byte; "John" 0x)
```text
The fourth day, the number of people went 1 hour is 1 hour, and he voles 2 equals <<1*2=8>>8 maleer.
The camer, Bill receives 40-300 = <<200-300=180>>180 minutes.
The number of people went and she will be 200 * 3 = <<200*3=4000>>6000 minutes per hour.
The total number of people went in one hour, how many more people went in one hour?
The number of people went in one hour, Tom, Ery's number of people 
```

bankA4 framed, key stream 8, one draw (404 bytes, prompt 1.936 bits a byte; "John" 0x)
```text
There have 400 x 4 = <<200*4=400>>500 in his price Breen.
So the cost 3*5 = <<2*2=8>>80 basketer. How much riplit will it takes him for Catcher more pest week in total?
H flies weighs $25 on / 3 = <<70/3=6>>6
#### 6

Carmit's scores 1 at a play dowures 16 items cars. Altogether, Jime wants to eat twice beep. The slie make cassed 1000 minutes of watchures sheats long, and the rest of watches, 4 of the 
```

bankA4 framed, key stream 8, two agreeing draws (405 bytes, prompt 1.936 bits a byte; "John" 0x)
```text
The rates for 10 people is 60 - 5 = <<60+30=60>>60 years taking gold.
#### 10

Marcris has a puce then went age. If he has a shelding the number of steam will take a sheld for a total of $15 for his friend and he has a sheld for $50 each, how much does she need to sell?
The ruck that costs $50 each, and the rest are $50 each, calculate the total number of tead for the number of stead for the number of 
```

### foil4, prompt as written: 0 of 16 samples name John

foil4 as written, key stream 1, one draw (401 bytes, prompt 2.388 bits a byte; "John" 0x)
```text
Tue contains 100 + 30 years = <<60+60=120>>120 B than the same in the institch.
Then, the $20*.5*$3000 * .7 = $<<3/40*.25=16>>16 the two dollars.
Allymall cost 30/2 = <<30/2=105>>105
#### 105

Tomen is supplied at the drive to room.  If the madds Jas.  In one cup got of two years. If aygroup ree times, customery trice that cost $10000, how old is 9000 to the camed toy?
The number of boo cuit rain: 
```

foil4 as written, key stream 1, two agreeing draws (401 bytes, prompt 2.388 bits a byte; "John" 0x)
```text
There are 30 - 8 = <<60-18=30>>30 years old.
#### 40

The first still has 10 miles per second, and Cania's turtles have already has steads to make a squirds to eat on the second game.  He has 3 turtles for $10 each. The number of basketermelons that are sweets each, how many minutes does he have left?
If he has 4 times as many sweets as old as Seaten, she has already is 27*4 = <<10*14=16>>16 cans.

```

foil4 as written, key stream 2, one draw (401 bytes, prompt 2.388 bits a byte; "John" 0x)
```text
Each for the has 10 years / 2 = <<30/2=2>>2 skids for the leafs
The two days, To is 2*out 3*.5=<<2*5*1=35>>35.
90+2=20 hours.
Soe an equals 16 x 6 = <<4*12=700>>700 works.
So, Mark receives 4 which means is equal to one d the playd-six = 14 years / 75 feam - 6 = <<29-6=18>>18 points.
#### 18

Trady take-air scook is blue for the total amount fressed at the market. What is the periamol. Palisliceda 
```

foil4 as written, key stream 2, two agreeing draws (400 bytes, prompt 2.388 bits a byte; "John" 0x)
```text
If Janio has 8 * 3 = <<2*3=6>>6 dollars.
#### 6

Tom has twice as many sweets as long as the fund, and fold his sister, A is going to hom and a day for $25 each. If he has a wears for $3.00 on each of the money for the next year. The next week she played $15 x $1.250 = $<<1.5=5.5>>5.5 hours to clean the basketball.
Thus, the total amount he is three times as much as the number of school is 200 x $
```

foil4 as written, key stream 3, one draw (400 bytes, prompt 2.388 bits a byte; "John" 0x)
```text
Christmboar sfve 13 people (2*10 = 2 new just for the sums.
The time find the time total book needs to be upsed the air.zet: 10 + 16 - 5 = <<40-un5=15>>15 pieces of cheese weighs.
Thus, Drun had 24 + 12 + 6 = 60 seconds = <<180+60=240>>240
The dole third clubtract the 40 to kindivide the same number of games by 500 calorients.
The dollars in the geginning like off so 1/2*50 = <<4*30/100=0.5>>s
If 
```

foil4 as written, key stream 3, two agreeing draws (400 bytes, prompt 2.388 bits a byte; "John" 0x)
```text
First find the total number of picks.
#### 4

Mika’s dogs have been her sister and Bob has a percentage of all the movient. The total number of cats for the first week, how old will it take for the first three days?
There are four week so 2*2=<<2*2=4>>4.
The seats in a school is 16 * 3 = <<12*3=28>>28 turtles.
#### 6

Tom is a is $25 each.  How much does he have now?
Com has to sell $600 - $510 
```

foil4 as written, key stream 4, one draw (400 bytes, prompt 2.388 bits a byte; "John" 0x)
```text
20 * 2/3 = <<20*2/3=3>>2 years before in the gy
Then find the difference: 30 pound so x 10*4=<<2*10=40>>40 hours.
Adaboy takes twice as many fereads as Pet, so 3*60 = <<4*15=60>>60 perongs
If Bob has 120 / 5 = <<80/5=200>>200 daments.
#### 60

Mark makes 10 both type every day is exercies to sevolv, and does, how many sittens did Janie did Mr. Match make 1/2*50 cups of flaged surquitche me to sadr
```

foil4 as written, key stream 4, two agreeing draws (401 bytes, prompt 2.388 bits a byte; "John" 0x)
```text
The total amount of money tickets of 90 * $80 + $300 = $<<50+200+3000+40=500>>500
#### 40

To purchased 2 problements, how many more pirds does Mary have left?
The total number of basketballs in the team is 200-400=<<200-200=200>>200.
The cost of the stock is 100*20=<<200*0=100>>100
The total number of sole sweets of the womature is $100/.5=<<20/100*.5=5>>5
#### 5

The total number of wheels are st
```

foil4 as written, key stream 5, one draw (401 bytes, prompt 2.388 bits a byte; "John" 0x)
```text
The third fogrou defurtly: 5 dozens/garre/ takes 20*2 = <<20*2=0>>40
Wenaren's 10 * 2 = <<150*2=640>>2
Siround was $60 - $900 = $<<50-850=480>>58 discakes.
#### 500

Lulie bought an 80 foots at the sone the weight, he has received bank as old bought per hour.  What is the total time, Bubreen have remaining to have than 4 mank sell now?
Chas at a on each month, each 1,000*.5=2000 minutes.
Thus, the 
```

foil4 as written, key stream 5, two agreeing draws (400 bytes, prompt 2.388 bits a byte; "John" 0x)
```text
The marks that he birthday for the 300+30 = <<60+40=60>>60 minutes per hour
#### 20

For 8000 minutes to women and sheed to C is 400 feet dition. The silvery tickets of his collection to raising a year, how many hours does he need to make each tickets for a new initially?
The solum is $20/hour * 2 = <<20*2=30>>30 minutes per hour.
The total number of still of manages is 60 * 6000 = <<20*120=5000>>
```

foil4 as written, key stream 6, one draw (401 bytes, prompt 2.388 bits a byte; "John" 0x)
```text
Mr * (A = 1/2=
N 20/3=<<20/3=15>>15 nailable years
Then divide the estaddd the book ala leave 4 00 hours to add in halve to work the first candy.
60*.5=0
So Luccie spent 3 * 2 = $<<12*2=14>>14.
Two gets.
Larior payment is 24*1= <<6=24>>24.
#### 6

Em sways remerred eginning to swill her gachels each his ban ornigh squat /weeks, his father is cats every $2 per hour?
In one day Annie earned 2*30 = <<
```

foil4 as written, key stream 6, two agreeing draws (403 bytes, prompt 2.388 bits a byte; "John" 0x)
```text
First find the total number of subtract the number of guit: 6 * 3 = <<24*3=26>>46
Then find the total time Carole has to find the total number of silver: 300 + 30 + 180 = <<60+40+40+50+150=200>>200
#### 500

Jenny has already had 50% of each. If each ticket the first suppliated the box is $1000, how much is two weeks?
The number of birds of food of 150 men is $600 x 1/ = $2000 per hour.
So the third 
```

foil4 as written, key stream 7, one draw (401 bytes, prompt 2.388 bits a byte; "John" 0x)
```text
Each day Tip travel is $6 x .6 = <<5*12+9=2>>2 points
Thimumixingm-people, 25 cookies dinning so the fund gold abyment because 40 x 80 = <<2*12=90>>90 girls.
He received 50 cabys, meaning he finds 20 * 5 = <<20*5=200>>200.
So, the second house is 60/100*200 = <<20/100*200=200>>200 anks to be $5She left.
#### 6

Mary can weigh 2 decag, and 8 dogs her sister, calculate the total cost of 12-shirts on 
```

foil4 as written, key stream 7, two agreeing draws (403 bytes, prompt 2.388 bits a byte; "John" 0x)
```text
If he has 6 hours to find how many basketers are left: 80 pounds/hour = <<240+80=100>>100
#### 200

A have been breaks this week. The points and seen where is 40% of them all cards per hour. The club has 200 quilets of his friend, and his mide, and she has 20 people at the end of the portle, how many sweeks did he need to be on his hom and a women?
If he has to sell $5 each, how much does he need to 
```

foil4 as written, key stream 8, one draw (403 bytes, prompt 2.388 bits a byte; "John" 0x)
```text
To 30*30 = <<10*30=400+5+00=60>>60 breats.
So the clith sides was 1000*60=<<1000*60=7000>>20,000 / 15 40 = <<7000/150*1000/100*3000=100>>100
The total number of cats are left is 100 * 1/2*5 = <<20*1/5=6>>6
Oboo purchases from the same spitch the wheed who can hold .300+100=<<500+2000+100=6000>>2000 fem spens
So calculating day:000 hours.
Hal is each doll, this chicken make 400 - 10 = <<1000-10=300>>3
```

foil4 as written, key stream 8, two agreeing draws (400 bytes, prompt 2.388 bits a byte; "John" 0x)
```text
There are 100+12=<<100+12=105>>50
#### 50

Michael is his heam off a 100% of $1500. If he gets a $500 for the store and Ben and Sunion has 100% of $20,000 bill is $2000 for the number of kg of a rate of his work and 50 feet by 100% of the remaining. If Combined like traveled by the number of mages per hour, how much cheam is this week?
The smallest brother is 50+20=<<20+20=100>>100.
So he has 300 
```

---

## Report: pass5

PC run, pass 5 (second of the four amended-key passes)

Reading: no sample answers the question. The subject surfaces for the first time, framed:
- bankA5 framed, key 1, one draw: "…students to find the library from Carly, John spends the ceen a year." This is John with "a year", inside an answer line.
- bankA5 framed, key 2, two draws: after "#### 5" a question opens "For a shelter, a sheld of a shelter, a shelter…", which is the prompt's noun, looping.
- As written: 0 of 16 bankA5 samples name John. Framed: 1 of 16.
- foil5 as written: 1 of 16 names John (key 5, one draw: a new question opening "John has 45 D is brew…").
- No sample contains "volunteer" or 72.
- The prompt codes worse than after pass 4: bankA5 2.507 bits a byte as written (bankA4 2.224) and 2.386 framed (bankA4 1.936); foil5 2.670 (foil4 2.388).

Held-out: bankA5 1.597 bits a byte (bankA4 1.610); foil5 1.803 (foil4 1.822).

Timing: bankA5's largest window was 158.9 ms, above its 153.9 ms bound, while its mean stayed at 136.1 ms. The stop reads the mean, so the run completed. bankA6 is projected on 158.9 ms: 1311 × 158.9 ms + 4.48 s = 212.8 s, deadline 213 s. foil6 is projected at 107.2 s, deadline 108 s. Both are running now.

## Pass 5: amended key (29b76d727), banked bankA5, bankless foil foil5

**bankA5**: PROJECTION 1311 x 153.9 ms + 4.48 s = 206.2 s (153.9 ms: the largest window measured on the amended key, devK_bank beside devK_foil; bankA4's windows ran 119.8-143.7 alone; 4.48 s the largest held-out read, devK_bank); DEADLINE 207 s (runner timer and outer timeout); early stop when the mean section time passes 153.9 ms; RAYON_NUM_THREADS=8, beside foil5
measured: wall 183.3 s (0.89 of the projection), peak resident set 382976 KiB; `RUN_RECEIPT exit=0 wall_s=183.3 peak_rss_kib=382976 user_s=1225.1 stopped=no`; windows 120.2–158.9 ms, mean 136.1
`TOWER_PASS pass=0 train_bits_a_byte=1.560 dev_bits_a_byte=1.597 dev_regions Q=1.811 P=1.334 N=2.289 M=1.170 deposits=1311/1311 pass_ms=182866 elapsed_ms=182896`
state bankA5/STATE sha256 a0e83c883ea2e065b57e6706cdc6320ce7ddd7baccf25a30bfa33f6ce175718d

**foil5**: PROJECTION 1311 x 79.4 ms + 3.11 s = 107.2 s (79.4 ms: the largest window measured on the bankless law, foil4's pass beside bank4; devK_foil 74.3; 3.11 s foil4's held-out read); DEADLINE 108 s (runner timer and outer timeout); early stop when the mean section time passes 79.4 ms; RAYON_NUM_THREADS=8, beside bankA5
measured: wall 98.1 s (0.92 of the projection), peak resident set 230424 KiB; `RUN_RECEIPT exit=0 wall_s=98.1 peak_rss_kib=230424 user_s=578.9 stopped=no`; windows 70.8–73.9 ms, mean 72.3
`TOWER_PASS pass=0 train_bits_a_byte=1.760 dev_bits_a_byte=1.803 dev_regions Q=1.899 P=1.696 N=2.462 M=1.281 deposits=1311/1311 pass_ms=97671 elapsed_ms=97700`
state foil5/STATE sha256 f266c2e66bcfb47c9e62378d054d20c6e9f2386e9f1e031e411fb2fffe02ddcf

### bankA5, prompt as written: 0 of 16 samples name John

bankA5 as written, key stream 1, one draw (400 bytes, prompt 2.507 bits a byte; "John" 0x)
```text
Table the cost is 3/4*8=<<1/2*8=20>>20 more watts
She makes 24*10= <<120*.5=2#### 40

A feet of paper hour. How up is 7 basebects uling from his sala, Yver sell his game, and $ero and By got in pards of two more than the passenginses of these parents as many passengines as now. How many people are done to read she wait for to the exercise?
Flinia spent 5 remainingcveries, Dian rate 2 × 4 = <<2*4=
```

bankA5 as written, key stream 1, two agreeing draws (400 bytes, prompt 2.507 bits a byte; "John" 0x)
```text
The first twice as much as the sum * 5 hours = <<2*7=24>>24.
The total before three times as 80 seconds, 3*1=<<6*1=16>>16
The two of the flour is 150+40 = <<70+40+40+40+80+120+3000+2000+2000+200=120.00
#### 4000

Michael, and burns at a seater for a seater for a seater of $1 to each of $30000 each of $1, and is $1. If this amount for a seater for a seater for a seater of $1, how much did he have s
```

bankA5 as written, key stream 2, one draw (400 bytes, prompt 2.507 bits a byte; "John" 0x)
```text
In the number of calls last week, for the number of encils/sheed / 16 = <<18/2=8>>8 tens
It takan to T = 2 * 3 = <<3*3=6>>9 proot left.
After ten / 3 = <<3/3=1>>1 more blue marks.
4 + 5 = <<1+5=6>>6 cookies
The visiered evening 9 * 2 = <<6*2=6>>6 cubic tens
Ben take x 150 = <<2*7=2200>>200 more people.
Altogether, Duz spends 20 * 20 = <<20*20=120>>120 years.
He has a litch of each 20/1000 - $25 = 
```

bankA5 as written, key stream 2, two agreeing draws (400 bytes, prompt 2.507 bits a byte; "John" 0x)
```text
If Rix, subtract the basket: 500 - 10 = <<100-15=50>>50 minutes
#### 50

A downs to make a shelond is $700. She has $250, how much did he save by $700, how much will be left after he save by $250?
First find the total number of pencils find the total number of people save by $.by the time to find the total number of people not need: $250/.50 = <<250/.5=200>>200.
#### 50

Story has 100 mead of his 
```

bankA5 as written, key stream 3, one draw (400 bytes, prompt 2.507 bits a byte; "John" 0x)
```text
Monday Michael: 1, *2,0
She bought 2 units number by the is the combined expercentagain, then 45*500 = <<15*200=100>>100
So it in the x be the price was original 20% * 100% = 45,000
Then find how many people were adding: $200, and 10% of  to get third year, the first shirt increass 20/100*40=1500: $1.25+$10,000 = $<<15000+200*40=200000>>5000 feet
#### 200000

The osixark cost length and she collec
```

bankA5 as written, key stream 3, two agreeing draws (403 bytes, prompt 2.507 bits a byte; "John" 0x)
```text
First find the total number of subst: $200 - $12 = $<<100-12=40>>40
Then find the total number of subst: $12/2 = $<<20*2=50>>50 people in the basket
Then find how much money find the total number of subst: $12/strucks * $12/strucc = 
Then find the total number of substructs
Then find the total number of substructs
Then find the total number of substructs
Then find the total number of substructs
Then 
```

bankA5 as written, key stream 4, one draw (400 bytes, prompt 2.507 bits a byte; "John" 0x)
```text
If Rissing time A total of 5 zale * (carg = -
First, Marc, Mark is equally 8 * $2 + $6 = (.5+$.15= $100 which repen."
#### 250

Ten's azon needs of sampeets and 75 every 6 hours. Wench has twice as damer everyone and Collyer Mark ate 2 commodes. Iver is twice as old as Miotel and Barricium. Sarry is 200 00/4 = <<2000/4=6>>6 locks. The total month that feet of citer emorith two year, Let the first 
```

bankA5 as written, key stream 4, two agreeing draws (401 bytes, prompt 2.507 bits a byte; "John" 0x)
```text
The total amount he is (2/3)*$600 = <<1/4*600=100>>100
So he is 100*100=<<200*100=200000>>20000
#### 200000

Tom is $120 in a week. If Bris is $4000 in a week, how much will the first week, he spend his working?
The total amount of money that is $120 / $120 = $<<200000/120=50000>>20,000
#### 50000

Tom has a day, how many calories did he can have left?
The total amount of money to be seved for $400
```

bankA5 as written, key stream 5, one draw (401 bytes, prompt 2.507 bits a byte; "John" 0x)
```text
The total person has $e two times as mchalls because 3 times Jan = 
Then find the total cost of the pear: $8/7 = <<6*6=40>>4
He increases that she way:$28 because .50 * .7 = <<20*1=30>>30 ounces of flow: 12 greway: 20 - 2 = <<100-2=100>>100
So everyonn’s dah payler is 50+100*40 = <<100+100=200>>200 cars.
He left 50*200=<<100*200=500000>>64000 dimate teas.
If that is 20 /month, .25/gallon is 60 - 
```

bankA5 as written, key stream 5, two agreeing draws (401 bytes, prompt 2.507 bits a byte; "John" 0x)
```text
The total price per supplium 40*200 = <<6*200=200>>200
So he is $5*$50/.5=<<20*.5=20>>20 people at the stead.
C game by 100%, the total number of supplium game for a total of $5 * 6 = <<5*200=300>>300.
#### 500

Tom is currently math tructon, and Michael is making for the tree is equal to $120 each. If he has 100% of his friend is equal to $100*$100/$100/$100/$100/$100/$100/$100/$100/$100/$100/$100
```

bankA5 as written, key stream 6, one draw (401 bytes, prompt 2.507 bits a byte; "John" 0x)
```text
When the bread received 2/.5=20 hats.
If one slice gave Comindy 240/4 = <<240/4=20>>20
So of the gether after the molve times that month, the hook from Com is 5 glegs is 40 + 40 + 60 = <<160+60=248>>8 goals in the nice
#### 620

Tue, the Hormelbell has to volds he can pay 2 hours each hour. 60 chrees, Kina owns while Benarlared stay .5 less than two for costs $12 $3.00 each to pay for a swat which 
```

bankA5 as written, key stream 6, two agreeing draws (400 bytes, prompt 2.507 bits a byte; "John" 0x)
```text
First find the total number of subtract the hea
Then find the total number of subtract the remaining: 30 cars - 6 - 3 = <<24-3=8>>8
Then find the total number of subtract the hea: 30 cars * 3 = <<30*3=60>>60 
Then find the total number of subtract the hea: 30 cars / 3 days = <<60/5=40>>40
Then find the total number of sub: 30 cars - 500 - 6 = <<100-40=100>>100
Then find the total number of subtrac
```

bankA5 as written, key stream 7, one draw (400 bytes, prompt 2.507 bits a byte; "John" 0x)
```text
In total, there conve 12 + 6 = <<12+6=42>>42.
Cudget and double the number of polds there he bak: 30 gainings/crun – 11 = <<2-15-pricity of bakesl takes 4 degree hat’s fastin servation Saturday.
Thus, they have 24/2 = <<12/2=6>>6 cars.
In total, the total squiral - 8 students + 12 cars.
The difference is had 24/6 = <<24/6=35>>300.
The cars have a total of 4 * 8 = <<8*8=76>>102 hours every week
```

bankA5 as written, key stream 7, two agreeing draws (403 bytes, prompt 2.507 bits a byte; "John" 0x)
```text
If he has 8 hours, we have 15*4 = <<10*4=100>>100
Tom be the cost per hour: $3 people in a is $3*.1 = $<<5*.1=2>>2 dollars.
#### 1

A total of 5 feet per hour. The number of people in value of the week off the lake when he is twice as much as the total amount of money. The first, how many people in value of the tead left after it cost?
The first three years, we have a total of 2 * 1 = <<2*1=8>>8 hour
```

bankA5 as written, key stream 8, one draw (403 bytes, prompt 2.507 bits a byte; "John" 0x)
```text
#### 5

Davy buys 3 both sides of team turchamages as avium for her gavium is $40 = $24 square pon mages to raiser. If he cost 11 hours at 10 per weeks, the paration, turing together is 1 hour at $12, then both sides than Mike every play in, how many muthers?
He spends 10=<<2*40=8>>20.
He gets pasach of and cents are boxal is $120/.5=<<300*10/100=40>>40 people in-2vaces
Nor for the marks three times 
```

bankA5 as written, key stream 8, two agreeing draws (400 bytes, prompt 2.507 bits a byte; "John" 0x)
```text
The number of sead is 60 + 20 = <<20+20=40>>40 minutes
The number of seeding the number of sead is 60 + 4*5 = <<20+45=40>>40 minutes
Then add the number of sead is 60 / 3 = <<60/3=50>>50 breaks.
The total number of sead is 60 + 12 = <<60+12=150>>150 breaks.
The number of sead is 60 + 50 = <<60+50+100=150>>150 breaks.
The number of sead is 60 + 30 = <<60+30+30=90>>90 people at the break.
#### 270


```

### bankA5, prompt framed: 1 of 16 samples name John

bankA5 framed, key stream 1, one draw (403 bytes, prompt 2.386 bits a byte; "John" 1x)
```text
There are 1 * 2 = <<3*2=3>>3 movel that costs $9.
4 hours at 5 books x 20 sion so she (200*.5+$2.25=<<90+20=800>>600 students to find the library from Carly, John spends the ceen a year.
#### 20

Fonce Dave by both of fulled and milk order Joight is 12. Dave by pared.  Jim has only once at a purchasuch is 30% only rip. Ambirds the librar banana cheraty, there he has 2*30 pulfills to a read. How long 
```

bankA5 framed, key stream 1, two agreeing draws (401 bytes, prompt 2.386 bits a byte; "John" 0x)
```text
The second water is equal to a certaurant and twice as 10 bananas, so he has to her new because (2/(.5*.)*.25=<<(.5*.25=.5=5>>5
#### 5

Tom has 15 days. She gave out how many mom has this week?
The total number of baskets is equal to $1 x $1 - $2 = $<<1+2=3>>3.
Therefore, she will spend $2 * $2 = $<<2*2=4>>4
So he has 40/2=<<80/2=20>>20 minutes per hour.
#### 20

A bought a traight, how many hours 
```

bankA5 framed, key stream 2, one draw (401 bytes, prompt 2.386 bits a byte; "John" 0x)
```text
Each as Donon's equation and 6+3 = <<2*3=6>>6 cats.
Since the trofit takes a third internice: 3 hours * 15 bananas = <<1*2=20>>20 study hours 
The remaining likes he needs 2*5 * 10 = <<2*50=50.00>>20.00.
The building, he known at a is 24*$25=$<<30+50=450.00>>400
The movest of 9 00% of his er oyrip by the derier than they both: 300 / 100 = <<2000*25=250>>250
#### 2000

A subtracted a total of $25th 
```

bankA5 framed, key stream 2, two agreeing draws (400 bytes, prompt 2.386 bits a byte; "John" 0x)
```text
If he is $3*.5=<<6*.5=4>>4 feet
#### 5

For a shelter, a sheld of a shelter, a shelter, a shelter, a shelter, a shelter, a shelter, a shelter, a shelter, a shelter, a shelter, a shelter, a shelter, a shelter, a shelter, a shelter, a shelter, a shelter, a shelter, a shelter, a shelter, a shelter, a shelter, a shelter, a shelter, a shelter, a shelter, a shelter, a shelter, a shelter, a shelter, a sh
```

bankA5 framed, key stream 3, one draw (402 bytes, prompt 2.386 bits a byte; "John" 0x)
```text
Each both sides left +8* = <<12*3=8>>8 bottles.
So, Jos, the buy the number of feet long to Larvole towle, Wates need to Rate will have 12 both sides, he purchase is 12 + 20 - 9 = <<360-34=6>>6 full
Then find the year subtract the end of the total time to find the time James soff 200
/ 4 hours/hour = <<6/4=6>>6 students musts
#### 44

Carbed and his new in the home?
If there were twice the distance 
```

bankA5 framed, key stream 3, two agreeing draws (400 bytes, prompt 2.386 bits a byte; "John" 0x)
```text
In one 10 people are worth $3*$3*$3*$3*$3*$3*$3*$3*$3*$3*$3*$3*$3*$3*$40 = $<<2*3*20=40>>40
He increased to find the total number of cats by the number of cats by the number of cats by the number of cats by the number of cats by the number of cats the full: 200 * $100/first/(.25)*$100/(.25)
He spends $80/(.25)*$15000/(.25)
He spends $80/(.25)
He spends $80/(.25)*$80/(.25)
He spends $3*$6 = $<<3*$8
```

bankA5 framed, key stream 4, one draw (400 bytes, prompt 2.386 bits a byte; "John" 0x)
```text
If Saturday his tin his whily they land, she tures can grow 40/4 = <<16/4=5>>5 hours.
The se?
First, Dix has 3 hours / 2 = <<1*2=8>>8 goes
That * 3 hours + 9 + 10 = <<7+5+10+1=60>>60 for fy the distance
Total value has 3 hours + 5 car = <<3+8=8>>8.
Michael school friend Mato * 2 tr = <<2*3+10=36>>36 for the brare.
#### 18.

It is 10% of them were long. So each the raire is $200 for the rolled for 
```

bankA5 framed, key stream 4, two agreeing draws (400 bytes, prompt 2.386 bits a byte; "John" 0x)
```text
The total amount he is $10+$1.5 + $1.5 + $40 = $<<2+15+20+15=90.00>>120.00
The total amount he is $12 / 2 = $<<4/2=.00>>.5 left
The total amount he earns to find the total amount he is $6/hour to find the total amount she spends dinning: 30 minutes * 2000 = <<60*200=300>>300
#### 2000

The number of people for the hott of his save has to his school is $50, and he gets a certaurant and is $100,000 
```

bankA5 framed, key stream 5, one draw (400 bytes, prompt 2.386 bits a byte; "John" 0x)
```text
The other neighbors (kg
If 10 40-20=<<60+0=10>>10
#### 15

Greis  of the door tree on higher to drane turn twice as Redde. The next day 5% of the playnects of father to only set of foot started. If each last four talliles less than, 75 oz is saved 40/5 weeks and other friends, the number of cats in the paratissist to new pfency's money, his number of more cows in the parial for the oncom to cludee
```

bankA5 framed, key stream 5, two agreeing draws (403 bytes, prompt 2.386 bits a byte; "John" 0x)
```text
The weekend ubtracted the tripe this means three times the number of structer than the trip, $3*$3*$3*$3*$3*$3*$3*$3*$3*$3*$3*$3*$3*$3*$40 = $<<2*3*$3*$15,000 = $8 per hour.
He has $80 x $80 = $<<3*$80 = $<<6*$80 = $<<80*$80 = $<<5*$1.x $250.
He has $120 - $15 = $<<120-1.5=20>>20 years old.
He gets a $100*$15=$<<100*$15=$40
Then add the amount for the first day, the total number of bikes to find the 
```

bankA5 framed, key stream 6, one draw (400 bytes, prompt 2.386 bits a byte; "John" 0x)
```text
When the bread Mr. Drjection hae, the current present together there are a total of 6 cars - 30 shel = <<60-8=40>>40 minutes per years.
If she make 70 miles speed -3 paurchassizoo because she final a total of 40 + 5 = <<60+5=90>>90
To read waroares 48*.06 = $<<3*500=5000>>50,000
To cocer bealeight in 2 find or the talling lail: $900 - $80 + $200,400 - $40 = $<<2000-2505=creams left by the procelt

```

bankA5 framed, key stream 6, two agreeing draws (400 bytes, prompt 2.386 bits a byte; "John" 0x)
```text
First find the total number of subtract the number of subtract the number of subtract the number of subtract the number of subtract the number of subtract the number of subtract the number of sub: 400 strips/find the total number of subtract the number of subtract the number of subtract the number of sub: 400 strips/chas: 160 - 700 = <<1000-150=50.00>>25
#### 150

Michael has to his house to sell 
```

bankA5 framed, key stream 7, one draw (400 bytes, prompt 2.386 bits a byte; "John" 0x)
```text
In total hours, Cary receives Japer bill + 24 + 2 = <<24+2=14>>14 times
#### 32

A is twice a local hop and than the mom. It buys 5 marks that Mad is a discount of cookies. How many standballs did Capritem on the first week?
The buey' weighs 5 minutes by 60 rows of id and Because  shamp a total of 5*4 = <<2*7=260>>2 block
#### 6

Ben the end of the dogs in the first day his friend is 40 - 10 = <<4
```

bankA5 framed, key stream 7, two agreeing draws (402 bytes, prompt 2.386 bits a byte; "John" 0x)
```text
If he has three times the price of whily bill and fast as Michael have 8-40 = <<120-40=30>>30 grocery before the original mays a week.
#### 60

The ceamated in the builver the first games and three times as many babysitting as Michael in a week. How many babysitting is It have?
The campick has 5 / 3 = <<20/3=6>>6 dollars for the first games.
The campick has 5+8 = <<20+8=20>>20 dollars for the first 
```

bankA5 framed, key stream 8, one draw (400 bytes, prompt 2.386 bits a byte; "John" 0x)
```text
This means he ate 6 slarge feet lene, and a money, to 60+18 * 13 boxes of pick-2+18 + 6 = <<32+18+18+6=184>>145.
Nevisa will he, there are now $220+6 = <<75+6=23>>28 large ey.
Ann's car sellin Malto the next store works with 12 / 3 = <<9/3=9>>9 dollars.
In trick has 5 peach. He sells thurtles there were 24 days on together they sell to buy 28*20 = <<8*100*10=40>>40 are worth .5 from the time : $10
```

bankA5 framed, key stream 8, two agreeing draws (402 bytes, prompt 2.386 bits a byte; "John" 0x)
```text
The number of seath of the remaining both sides is (.5*.)*.)*.6 = <<1*.6=2>>2.
#### 11

A has to catch the number of seam every hour. If he has to vole time?
The seam has already womes x 1/2*10 = <<2*1/10=2>>2 servings
He gets 2 servings in a day, so he needs 2*10 = <<2*10=20>>20 seam left.
The seam has to volve times the total number of seam has to volve times the number of seam has already has to 
```

### foil5, prompt as written: 1 of 16 samples name John

foil5 as written, key stream 1, one draw (402 bytes, prompt 2.670 bits a byte; "John" 0x)
```text
Tabby will take Angie must averagcaughted, +6=<<12+=3>>3 were needs
So $20*.9=$
Total earners for 30/20=75
Total needs to have played 30 loaves per largest contribution
15/12/1 = <<6/5*9=30>>30 on taxes
Then divide that amount by the number of kement mages by the father ssumm to the white in dollars.
Gold, she needs to purchased 110/2 = <<70/2=30>>30 ket
Then find the volestion for the player produc
```

foil5 as written, key stream 1, two agreeing draws (402 bytes, prompt 2.670 bits a byte; "John" 0x)
```text
There are 30 + 12 = <<60+18=60>>60 years old.
#### 80

The total number of suniblings on 200 curtles is 25 days in a subscripe and Jank has 30 minutes to sell for 20 polvents. Each qui has a sole for $3. If Bob has 30 days, it will be 30 years old, how many minutes does he have left?
If he has 3 times as much as the first day as his roll is 20+4 = <<8+4=8>>8 points.
#### 24

Total stars is twice as 
```

foil5 as written, key stream 2, one draw (400 bytes, prompt 2.670 bits a byte; "John" 0x)
```text
Since the datch watermely 4 volen it received 70 feet of father per month, he uses 200 yards for 1 hour for 30 cards because 7 x 2 = <<15*2=30>>30 gave
So in total both sides of them himbeed Grancaco: 800 - 4 = <<240-85=150>>150 feet
#### 1000

Wiin A some for the endethewing solts trancycles three times as the number of adults while Clyrouts. How many years does he sell allowing for the two direc
```

foil5 as written, key stream 2, two agreeing draws (400 bytes, prompt 2.670 bits a byte; "John" 0x)
```text
If Emmy has 60 - 2 = <<60-2=30>>30 people in the squird.
#### 5

For a sha weighs 3 barts and he has to sell it of his breaturtles and 20 bottles of just and 80 miles per hour. There were 400 feet deed of her house. If Mary has a quarter is 12000 mium for the flag, how many jobs does he have left after there if she is at the before if she has two duts and the rest are still and a surtle port?
The 
```

foil5 as written, key stream 3, one draw (401 bytes, prompt 2.670 bits a byte; "John" 0x)
```text
Station receives 30 gumbbs * 12
students / 14 bries/hour = <<3*180=40>>40 games
#### 50

Dean bought an questones it will were 1050>>50 littles in an hour, each pairs each commudshrooms. How many people need Ben is working for the company and received by her brother receive?
Let N be the number of anglene chapters scored 2.
If Breek gives heat their mail's 25 - 2 = <<2-2=6>>6 points.
Poppoon had 6 
```

foil5 as written, key stream 3, two agreeing draws (404 bytes, prompt 2.670 bits a byte; "John" 0x)
```text
First find the number of people can't find the number of beas: $100/day * 100% = <<100*50*.05=50>>50 dollars to find the total number of kg of spr
So he has 100-200=<<500-20=100>>100
#### 100

The school scored at an equal amount of money Jason.  If he has 200-30 minutes per hour, how many minutes are there in the dimball cards?
The campons has 50 miles per hour, so he has 40 sweets * 2 = <<20*2=16>>1
```

foil5 as written, key stream 4, one draw (400 bytes, prompt 2.670 bits a byte; "John" 0x)
```text
If Michael how mare two kates does Comia have alie?
The games in 20 more servings did Rust of 2 x 2 = <<2*2=6>> the week.
Hannah has 2+4+3 = <<1+3=9>>6
14-6=<<8-3-6=6>>6 cups.
Heather is a play, there are 22 + 3 – 3 = <<28-3=6>>6 minutes.
Thus, he has 8 so 87/8 = <<8*7=4>>4 chalvates.
#### 3

Carl was wear that of the first. His still has twice on wait used to aster she has 3 tickets, before tow
```

foil5 as written, key stream 4, two agreeing draws (400 bytes, prompt 2.670 bits a byte; "John" 0x)
```text
The total number of stitches traveled 7*12 = <<10*6*50=100>>100 gold now.
#### 20

Tom has inclims a sheld tickets of what is the new ceed?
The require has 25 - 3 = <<2-3=2>>3 years old.
#### 2

Tom has 20 people can make a supplial. What is the total time she has left after he steam alto the crayon?
Half Martmy has to have a total of 3 * 2 = <<3*2=8>>8 miles per hour.
#### 6

Sarah has twice as m
```

foil5 as written, key stream 5, one draw (401 bytes, prompt 2.670 bits a byte; "John" 1x)
```text
The problems $0.5*500)/5= <<0.0*.45=6>>6 cookies
#### 32

Mile bought in praceler. His weeks?
John has 45 D is brew the 27 x 12 = <<14*18=36>>36 feet.
Since Tuesday Randing has 166 * 12 = <<48*46=240>>246 pieces.
He has to arree time, he game is 18*5=<<120+185=70>>220 in dollars.
#### 450

A nails A to her 80 old colon. If each movebe is $5 each.  How much did he bor?
Firstsubtracted 50/4 = <<50/2=
```

foil5 as written, key stream 5, two agreeing draws (404 bytes, prompt 2.670 bits a byte; "John" 0x)
```text
The first store we get $24 + $120 + $6 + $2.5 + $48 = $<<35+112+27=56>>280
#### 290

Milli is $3.00 each. She has 6000 seconds up to his games to be set of money. She has to buy a 80 miles per hour. If Carole bought is $500 for the femperature sweets, how much did he have?
The total amount of money that amount cost $1000 per hour * $1000/5000 = $<<5000*.250=50.00>>500.00
#### 2050

Amen is $3000 each 
```

foil5 as written, key stream 6, one draw (403 bytes, prompt 2.670 bits a byte; "John" 0x)
```text
Let X be the femperation Sana.
And is 8 / 4 = er fruits
James is + 3 = <<+3=2>>2.
Therefore, Delling because C- el = <<-=2>>3 >>2
#### .5

Dascanel has six times and half as many boys and they shipered that through 9.
Scher has 3/4-2+18 answered with inclub and she hawalling 4 hours per hour. If Fince who repper tickets women, she remains that 300 calories were 12=<<40% C end up three times that each
```

foil5 as written, key stream 6, two agreeing draws (403 bytes, prompt 2.670 bits a byte; "John" 0x)
```text
First find the number of bottles of fruit: 4/2 = <<20/2=4>>4.
So in total, we know that is 60 - 5 = <<60-5=30>>30 people to work.
#### 30

Emm's dogs have there are 30 students in the bead spruce.  The fourth of the sprofit will be 12 years oldest as old as Phoger. In the first day, he trained 40-40 = <<120-60=24>>24 pieces of clothes.
#### 24

Carole has twice as old as the first day.  Atem, he has 
```

foil5 as written, key stream 7, one draw (402 bytes, prompt 2.670 bits a byte; "John" 0x)
```text
Since he has already eats 1

A balls sweeks in 10 hold now, you have the somelied 2-6 = <<.8=2>>2. Then ade two- the second wide, Yesterday with 5 motors order than her sister end of Runit with his basketball per hour.
The pens 50 pairs of paint is ther is 50 id every hour, the platel, then it had 7080 / 2 = <<360/2=<<60*2=50>>50 pirtes of mile from the resemperat.
#### 20

Metta is 20% of food for 
```

foil5 as written, key stream 7, two agreeing draws (400 bytes, prompt 2.670 bits a byte; "John" 0x)
```text
If he has 5 hours to eat 15 + 3 = <<1+3=3>>3
The countries were saw and 7 people on the bank?
The music is 2*2=<<3*2=8>>8
The second supplial is 3*2=<<2*2=4>>4.
So in total, the surtles will be 3+6 = <<6+6=12>>12
#### 6

Michael has 30 years old. If the hill has 30 years to dig a flag?
The smallest brother is 18/60=<<180/60=6>>6 square feet
#### 5

Michael has two friends are still for each, and f
```

foil5 as written, key stream 8, one draw (401 bytes, prompt 2.670 bits a byte; "John" 0x)
```text
To * 35 = <<2*15=6>>6 L
Arone use a total of $600/3 = 300
#### 200

The number of ucks' sones will be colleces to get a each floor. The total number of apple bars feeds of (60 feet flowces for 400 feet/pick saltog the company gift /100) = <<20/100=5>>5 ropers is track from the same storer be.
Sum were cated 6 - .2, and wears is 8 + 5 = <<6+5=5>>5 minutes.
For donation, And cakes 240+80+$500 = <<300
```

foil5 as written, key stream 8, two agreeing draws (400 bytes, prompt 2.670 bits a byte; "John" 0x)
```text
There are 7*3 = <<2*13=6>>6 seconds.
#### 26

The buses has two dogs and his movels and B has 44 bottles of camp. If he spends a caps for a city is 15 in Julient. This week, she has 80 for the two square feet longer than the third of his friend and for $200 for her sister and she gets a new roll for 5% check. This week. The total number of blue marshrooms and Cales, and A walks to buy a $3000 per 
```

---

## Report: pass6

PC run, pass 6 (third of the four amended-key passes)

Reading: no sample answers about John.
- As written: 0 of 16 bankA6 samples name John.
- Framed: 1 of 16. Key 1, one draw: after "#### 250" a new question opens "John eats 1/6 as much as 2 cupcakes…".
- foil6 as written: 0 of 16.
- No "volunteer" or "shelter" anywhere. The one "72" is inside 2720.
- The prompt codes at 2.767 bits a byte as written (bankA5 2.507, bankA4 2.224) and 2.225 framed (bankA5 2.386). foil6 codes it at 2.557.

Held-out: bankA6 1.599 bits a byte (bankA5 1.597); foil6 1.785 (foil5 1.803).

Timing: bankA6's largest window was 159.3 ms, above its 158.9 ms bound, while its mean was 135.9 ms. bankA7 is projected on 159.3 ms: 213.3 s, deadline 214 s. foil7 is projected at 107.2 s, deadline 108 s. Both are running now.

## Pass 6: amended key (29b76d727), banked bankA6, bankless foil foil6

**bankA6**: PROJECTION 1311 x 158.9 ms + 4.48 s = 212.8 s (158.9 ms: the largest window measured on the amended key, bankA5's pass beside foil5; 4.48 s the largest held-out read, devK_bank); DEADLINE 213 s (runner timer and outer timeout); early stop when the mean section time passes 158.9 ms; RAYON_NUM_THREADS=8, beside foil6
measured: wall 183.1 s (0.86 of the projection), peak resident set 382116 KiB; `RUN_RECEIPT exit=0 wall_s=183.1 peak_rss_kib=382116 user_s=1223.4 stopped=no`; windows 119.8–159.3 ms, mean 135.9
`TOWER_PASS pass=0 train_bits_a_byte=1.542 dev_bits_a_byte=1.599 dev_regions Q=1.809 P=1.348 N=2.228 M=1.181 deposits=1311/1311 pass_ms=182598 elapsed_ms=182628`
state bankA6/STATE sha256 4b54c9da029355636ea9b6c371141c90e6b904bcc18a78372a0e020a22729370

**foil6**: PROJECTION 1311 x 79.4 ms + 3.11 s = 107.2 s (79.4 ms: the largest window measured on the bankless law, foil4's pass beside bank4; foil5's windows ran 70.8-73.9; 3.11 s the largest held-out read, foil4); DEADLINE 108 s (runner timer and outer timeout); early stop when the mean section time passes 79.4 ms; RAYON_NUM_THREADS=8, beside bankA6
measured: wall 97.9 s (0.91 of the projection), peak resident set 231508 KiB; `RUN_RECEIPT exit=0 wall_s=97.9 peak_rss_kib=231508 user_s=576.4 stopped=no`; windows 70.9–73.1 ms, mean 72.1
`TOWER_PASS pass=0 train_bits_a_byte=1.739 dev_bits_a_byte=1.785 dev_regions Q=1.887 P=1.683 N=2.407 M=1.220 deposits=1311/1311 pass_ms=97407 elapsed_ms=97436`
state foil6/STATE sha256 a8139b1c4cf9b81f7ed90da7c1b604a79a9eee260227006fde944a847a5c0e0e

### bankA6, prompt as written: 0 of 16 samples name John

bankA6 as written, key stream 1, one draw (400 bytes, prompt 2.767 bits a byte; "John" 0x)
```text
Table the lose girl total sides Ann spent and to find the 8eats will not need to find the total number of minutes of so
If 500+5*.8= <<100*.8=240>>240 for the first year.
Whad students have water to 500 - 30 = <<100+50=50>>50 people to sharw
Each of them is 500 - 100 = <<5000-100=2000>>1000
The rest of the galloncycles spends 500 - 100 = <<4000-100=300>>300 g
Together they need to his destment 200
```

bankA6 as written, key stream 1, two agreeing draws (400 bytes, prompt 2.767 bits a byte; "John" 0x)
```text
The second hour the weekdays he needs to find the total number of people remain: 6 = <<60=24>>24
The third of the travels (2/3)*.1=<<8*.1=8>>8 years old.
#### 8

Together, and 1/4 as many solds as old as old as old as old as old as old as old as old as old as old as old as old as old as old as old as old as old as old as old as old as old as old as old as old as old as old as old as old as old as 
```

bankA6 as written, key stream 2, one draw (400 bytes, prompt 2.767 bits a byte; "John" 0x)
```text
Each th tea m, the two suck, we get cones in x 1/6 = <<2*3=8>>8
#### 3

It this lollion each quirds prodone 3 mirds combining.  He's workgallon she has pree actors each taken Rodd Date, and pizzle for the items and aseball and the third day, HMill gos, the amount is 7 × 6 + 6 = <<2*6=28>>28 pies.
#### 14

Rize. Danize, and diplated his tomin two gainw. In 10 ssells if it will pay each with 6 popp
```

bankA6 as written, key stream 2, two agreeing draws (400 bytes, prompt 2.767 bits a byte; "John" 0x)
```text
The total number of beginning like terms is 5*60=<<20*60=240>>240 years 
The total number of beginning salculate the total number of beginning like terms in 5 years to find the total number of beginning like terms in 5 years to find the total number of beginning like terms by the number of beginning: 16 beginn = <<8*60=120>>120
The total number of beginning like terms in up: 30 years * 3 = <<60*3=
```

bankA6 as written, key stream 3, one draw (402 bytes, prompt 2.767 bits a byte; "John" 0x)
```text
Monass we find the probed 50*.% = <<15*.01=2>>2
Then add the cost per to find the proj of the reold the number of cookies the first 2 rows the third projing halveat that cost 500/3=<<60*0=280>>2800 for the coring mees
Then find the projie this inches: 1600 / 4 = <<200/4=2000>>450
Then find the proj number by 30000: 16 * 1/2 * .j.00
Then find the proj before: 2000 / 50 + 2000 = <<2000+2000=21000>>100
```

bankA6 as written, key stream 3, two agreeing draws (401 bytes, prompt 2.767 bits a byte; "John" 0x)
```text
First find the total number of moves find the number of moves Meginning: 20 x 2/5 = <<200*30=200>>200
Then find the number of moves by the number of moves by the number of moves by the number of moves: 50 miles / 600 - 100 = <<80000-50000=600000>>5000
Then find the number of moves by the number of moves by the number of moves to find the number of moves by the number of moves to find the number of 
```

bankA6 as written, key stream 4, one draw (401 bytes, prompt 2.767 bits a byte; "John" 0x)
```text
2 * 2/3 = <<2*2=4>>4 mix
The before pastry: 2 - 6 = <<20+6=18>>18
Madpoluel was 16*.2 * .4 = <<3*.4=87>>29
#### 41

A dollars must and he is has 2*5.5=<<7*5+10=330>>30 cup-plum.
Twice the resture of each both of them now 40 - 10 = <<50+60+30=650>>80
Pinvole every 20 minutes lesss, then the discounts was 50*100=<<50*100=400>>400/100/100/100*3*.5 weekly dog giftbaskets: 400 remaining = <<300*7=4000>>
```

bankA6 as written, key stream 4, two agreeing draws (402 bytes, prompt 2.767 bits a byte; "John" 0x)
```text
The total amount she has (2/5)*.5=2
The total amount he wants to find the number of mill: 200 - 8 = <<200-8=40>>40
#### 200

At the end of the team take to work for $50/$500 for the not. If Mian has $500 for the notage of he profit into 100/$50 = $100/$100/$100/$50 = $100/$100/$100/$100/$100/$100/$100/$100/$100/$100/$100/$100/$100/$100/$100/$100/$100/$100/$100/$100/$100/$100/$100/$100/$100/$100/$100
```

bankA6 as written, key stream 5, one draw (403 bytes, prompt 2.767 bits a byte; "John" 0x)
```text
The spose scored $.0(50 / $25 = 60
So the number of shefind the total number of books in amel
#### 40

This will take a vace for 3/3= two pick-27 = <<50+18=70>>270 pounds.
The second fish two bro takes three mage, pop goals and finished in 1 hour so that one-use's piects is 40 minutes ÷ 60 pounds = <<60*15=100>>100
He has half as many piects of ton sub akes to bac their purtles, so-start June brate 
```

bankA6 as written, key stream 5, two agreeing draws (400 bytes, prompt 2.767 bits a byte; "John" 0x)
```text
The total distance the birthday: 15*.5=<<10*.5=8>>8
The total distance Mike (100*.5=<<100*.5=200>>200
The total distance Mike he: 400 - 200 + 400 = <<100+400+2000+500=480>>480 minutes.
#### 480

Mato raise sandwich. If he is 80% of them for the first year, she will spend $2000 / $2000 = 5% of the week to both the total amount of the week. If he is 40% of the week, she will spend $3000 / $2000 = <<
```

bankA6 as written, key stream 6, one draw (400 bytes, prompt 2.767 bits a byte; "John" 0x)
```text
When the Erick takes 15*.1=$<<7*.1=2>>2.
He type has 12 - 5 = <<9-5=10>>10 mits
She hour 30>>30 mats leaves to the surbry the market
Durf the remains leaves 30 / 3 = <<60/3=50>>50 degrees: 15 minutes for 8*7 = <<2*40=1:0valing
He has 4 * 50 trworls/cip = <<10*4*50=240>>240 square ham
#### 680

Adam read is 5% one-$2 per hour.  Each sheet of his sistance is 50 degrees the stories and a stround, if 
```

bankA6 as written, key stream 6, two agreeing draws (400 bytes, prompt 2.767 bits a byte; "John" 0x)
```text
First find the total number of pickets by the number of pickets by the number of pickets by the number of pickets by the number of pickets by the number of pickets by the number of pickets from each day: 400/2=<<200/2=400>>40
Then add the number of pickets to find the number of pickets by the number of pickets to find the number of pickets by the number of pickets to find the number of pickets to 
```

bankA6 as written, key stream 7, one draw (401 bytes, prompt 2.767 bits a byte; "John" 0x)
```text
9 / 3 = <<18/3=6>>6 Ds
#### 3

Quesyan Boders in the same number of walking three mill Toon each turchaperfflag so, Dure, Jake start between 60 solves, Alice just earned that of 800 littles baskets.
Then subtracte the total distance cover game for the total point: 7400 leaves - 1880 - 18 = <<1880-18=1424>>14600 more than mider per hour.
The combined the number of hours total, Neve bought 20 - 18 = 
```

bankA6 as written, key stream 7, two agreeing draws (405 bytes, prompt 2.767 bits a byte; "John" 0x)
```text
The first 3 * 3 = <<2*3=6>>6 dollars.
#### 6

Carol is currently has already has to play. This freed and 15 rows of basketerms and 15 cars that math purtle wome.  The next hours, how many hours, did he have?
First, she needs to get gold is 8*12=<<5*12=120>>120 minutes.
The total number of people are when he has already has 18/5 = <<18/5=13>>25 cars.
Therefore, Saren subtract the first went to find the 
```

bankA6 as written, key stream 8, one draw (403 bytes, prompt 2.767 bits a byte; "John" 0x)
```text
We had 3 sells, 48*4 = <<6*4=48>>49
The total number of people could her takes 2 hour, 60 + 3,3 + 56 = <<3+35+48=185>>185.
Ian ay was 8*$24 = a total of $26/1 equiviil
That means he walk: 500 - 200 = <<200-200=400>>400
So they earn: 50 miles / 3 = <<100/3=80>>80 find the amount Joth prop's has
Frant briples 15 local tear takes by the total amount of Pogotel.
Tox  vestive to shipp = <<8*4=20>>20
#### 
```

bankA6 as written, key stream 8, two agreeing draws (400 bytes, prompt 2.767 bits a byte; "John" 0x)
```text
The total number of cents x 1/3*.60 = <<1*.60=60>>60
He has 60
He has 80 + 25 = <<18+50=180>>180 m
He has 120 / 3 = <<180/3=45>>45 people on B.
The engai is 3 * 6 = <<2*6=26>>26
He has 18 equal 18/4 = <<18/4=6>>6.
Since three times as many marshes as Rebrought is 6 * 1 = <<6*1=64>>64 from the number of still in the new ball.
Since three times as many cars as Roth mal is 6 * 3 = <<6*3=68>>88.
#### 
```

### bankA6, prompt framed: 1 of 16 samples name John

bankA6 framed, key stream 1, one draw (406 bytes, prompt 2.225 bits a byte; "John" 1x)
```text
Therefore, Simus Tom so Javed donought 2=<<5=25>>35 totals.
Verdie will spend $2 + $1.1*(30 add =  = $<<0.0*.1=5>>5
He gets 10 on the percentagra’s soda by 100*$120/50=<<100*.40=100>>100
#### 250

John eats 1/6 as much as 2 cupcakes as of them will seats to drink for his final in total. In the books it sells 5*$.25 = $<<100*(30% of the most cept Puid that Matth.
He has 40 hours less than to hea total 
```

bankA6 framed, key stream 1, two agreeing draws (401 bytes, prompt 2.225 bits a byte; "John" 0x)
```text
The distance the number of people are a total of 40 + 2 + 3 = <<20+3=110>>110 marks
Then find the total number of people in the 3 hours: 3 hours: 3 hours * 6/3 = <<2*12=8>>80 minutes
He has to sell 18 x .20 = <<18*50=80.00>>80.00
He has to sell it is $30 each month so she needs to sell it is $15/2 = $<<15/2=$30
He has to sell it is $50 x .50 = $<<5*50=200>>200.
The number of people on the first day
```

bankA6 framed, key stream 2, one draw (405 bytes, prompt 2.225 bits a byte; "John" 0x)
```text
Then find the number of busine tradie grous: 3 games + 2 goal = <<12+2=8>>8 the fecteck
Together the number of has to find the total distance total for the way: 4 jor 6+2 = <<16+2=6>>6 lem.
Cort Michael has 12 + 3 = <<18+3=90>>90 + 16 / 3 = <<65+22=225>>25 = <<600+6=40>>40
Michael buys 43*25=9 worth of orange kgupurcha.
#### 40

Valony needs to high a saving a new an hour.  If 500 feet were reach, the 
```

bankA6 framed, key stream 2, two agreeing draws (404 bytes, prompt 2.225 bits a byte; "John" 0x)
```text
If Lacob has 60 minutes / 10 square feet of 100/3 = <<100/3=100>>100
The total number of came rate of 40/15=<<20/15=40>>40 before this number 
He put 60 minutes to find the total number of came amount: 9/4 = <<20/4=5>>5 hours
So he makes 5*.10=$<<5*.5=5>>5
#### 5

The combined amount is home and Mase placed to $8 each, and 1/2*20 = <<2*5*.05=10>>10 minutes to see placed.
#### 10

Martha has 5% of the 
```

bankA6 framed, key stream 3, one draw (401 bytes, prompt 2.225 bits a byte; "John" 0x)
```text
Each both sides total tall-falls +20 = <<20+20=28>>28 hours for many people in the parold left
#### 3

The nack book  breakeets the first day’s house increased into 12 hours, which is 50 kg breaks which is 32000/3000 = <<2000*.25000=200>>200 dollars. The lengthmer costs $60.
So it rain100*10 = $600 an hour at the zill with total-150 = <<150+150=300>>300 minutes.
So it represented 50 gallon so he 
```

bankA6 framed, key stream 3, two agreeing draws (402 bytes, prompt 2.225 bits a byte; "John" 0x)
```text
First find the total number of people: $200 - $10 = <<100-50=100>>100
Then find the total number of people to the number of people to the number of people to the number of people to the number of people to the number of people to the number of people to the number of people to the number of people to the number of people to the number of people to the number of people to the number of people to the 
```

bankA6 framed, key stream 4, one draw (401 bytes, prompt 2.225 bits a byte; "John" 0x)
```text
If Rose have bought 6*30 = <<8*30=180>>180
Hencolic has 200 basprice per hour the bets of blow because 180 + 17 = <<14+17=126>>26 x 22
The bown in the originalf is 36/15+8 = <<7+8=325>>310 dollars in the lurcompls.
#### 225

Tome takes 3 fewer does he laxed by 2 days, and 3 turtle of Pratth, how many hour, and the louse is Granchie make a day?
The total amount of 200 bath turtle is 80+2+120+38 = <<
```

bankA6 framed, key stream 4, two agreeing draws (403 bytes, prompt 2.225 bits a byte; "John" 0x)
```text
The total amount of money, 5 * $5/2 = $5
He has $200 - $300 = $<<500-40=100>>100
The total amount of money to find the total amount of money: $200 - $5/2 = $5
#### 100

Carly's hotage of $10.  How much did he have left?
The total amount of money takes two of $10/hour = <<10*5=20>>20 passes.
The total amount of money to make $10/day * $10/day = $10/day = $10/hour.
The total amount of money that means 
```

bankA6 framed, key stream 5, one draw (400 bytes, prompt 2.225 bits a byte; "John" 0x)
```text
The total person has $.015 - $12 = 16
So the number of tred - 6 = <<8-5=.8>>26
So he covers he will have 120 / 3 = <<80/3=40>>40 left
Then find the number of ings: 4 for they left with a total of 60-60 = <<400-60=40>>40 ounces
Then find how many bikche
Josever the work is rep0/3=<<120/3=40>>40 dollars
So the amount from the two collecks 2=<<20*.2=250>>250
Then ad time the remaining: 4 feet of the 
```

bankA6 framed, key stream 5, two agreeing draws (401 bytes, prompt 2.225 bits a byte; "John" 0x)
```text
The first interest is $16 + $15/2 = <<18+60+1=54>>54 left
#### 540

Karia has 400 feet per hour. The first two stead wins is 150 basketers, and could home for 2 hours, how many hours did he save in total?
The first this means that are 12*3=<<4*3=120>>120 basket
The first three day he save is 150*3=<<30*3=90>>90 basket
The first three days, Dald is 150+12+12+12+12+12+12+12+12+12+12+12+12+12+12+12+12
```

bankA6 framed, key stream 6, one draw (401 bytes, prompt 2.225 bits a byte; "John" 0x)
```text
Mr. Past student 18 kast who bought 500 gallons/ouncard handment is 70 / 5 = <<180/5=20>>20 years old.
This means there is 500 - 40 = <<60-60=9>>3500 Pet of Ypar
So it had on 240/5 = <<160/5=25>>400
#### 40

Tab has 40% gembers and 14 people each. Suniirf00 cannand four feet of frocerture on the check mone. Prick has twod the distance from the of two times A-chocolate as much whig both that time. H
```

bankA6 framed, key stream 6, two agreeing draws (400 bytes, prompt 2.225 bits a byte; "John" 0x)
```text
First find the total number of pickets by the number of pickets by the number of pickets by the number of pickets by the number of pickets by the number of pickets by the number of pickets from each serving: 6*4 = <<12*4=64>>64 dollars per hour
Then find the number of pickets by the number of pickets by the number of pickets by the number of pickets from a year: 64 dollars - 32-13 = <<23-13=26>>26
```

bankA6 framed, key stream 7, one draw (401 bytes, prompt 2.225 bits a byte; "John" 0x)
```text
Angether Rachis now 3*.3=<<2*2=8>>8 years old
Then divide the original total sal the amount to dhe: 3 greaks - 16 * 0.5 = <<7*.4=7>>6 miles.
Hald is use, she – 3 = <<18-3=5>>5 times and the remaind that ree time to on the first how many both sides per bag after all hours?
First find the total time: 7 - 3 = <<7-3=9>>9 years old.
Ceginning Avat entrones left on the first day 3 * 3 = <<6*3=6>>6
The 
```

bankA6 framed, key stream 7, two agreeing draws (400 bytes, prompt 2.225 bits a byte; "John" 0x)
```text
If he has 3 hours to find how many people to the number of miles per hour: 6 - 2 = <<6-2=8>>8.
#### 6

A flies is three times as many hours as long as Paul and a rectravel in the previous day.  The first twice as many hours as Paul in the previous day and a shown and a shown is both miles per hour.  The first day his two hours, and a shown for a shown for $300 in a shown for $400 in a shown for $3
```

bankA6 framed, key stream 8, one draw (401 bytes, prompt 2.225 bits a byte; "John" 0x)
```text
There were 6+15 = <<18+30+13+80=200>>2600.
#### 2000

Berry is friend carry-months for the libruith sell maximp = <<20*.4=200>>200 cob days in the same Rho tree with. Martald only bear to burn babin piection it The company pm is equal to babis.  How much money will to the fabrice the new mead read 12 x carbabys in 25-400 = 8 nrierm that conse: .6*15 = <<12*1(70+2000=2720>>2, two by 90 for that she 
```

bankA6 framed, key stream 8, two agreeing draws (401 bytes, prompt 2.225 bits a byte; "John" 0x)
```text
The number of seath travels by 50*.5 * .5 * .50/10 = 
Then find the number of seath: 10 seath sides - 5 * .5 + 50/10 = 
Then find the number of seath: 8 / 3 = <<8/3=6>>6
Then find the number of seath: 16/2 = <<8/2=6>>6 years old.
So the total number of seath travels is 6 / 3 = <<8/3=6>>6
Then find the number of seath: 16 seath travels - 6 - 2 = <<8-2=8>>8.
The first hour number of seath travels is 
```

### foil6, prompt as written: 0 of 16 samples name John

foil6 as written, key stream 1, one draw (404 bytes, prompt 2.557 bits a byte; "John" 0x)
```text
Tob that finish time Marie is 1/2*6=<<1/2*6-8=8>>8 dollars to get anature on the 
6 × $.2in = <<8*.6=3>>3
The short dogs for 2 1 eggs because 7 + x = 8 - 5 = <<2+.5=5>>5
#### 15

Emy hunts at work of floor, which is the same amount of working. If he sprucks so in the gipt, the sheep has 100 children's play, then donates 3*2=<<3*2=8>>8 hours of corn teacher two gotels, 6 square feet per hour.
So they 
```

foil6 as written, key stream 1, two agreeing draws (401 bytes, prompt 2.557 bits a byte; "John" 0x)
```text
There are 30 + 6 = <<30+8=28>>28 feet
Then find the number by the number of cats per hour: 600 calories = <<600*2=2600>>600
#### 600

Martha has 30 minutes to make a stock and 400 feet and the rest are freed. The seats this year, Jake has 20 books and half as many hours per hour, how many pages does he need to buy after full?
If Tom has twice as many pickets as old as Jani, and seats this amouning 
```

foil6 as written, key stream 2, one draw (400 bytes, prompt 2.557 bits a byte; "John" 0x)
```text
Each of 3 turtles cost $12/15 = $<<24/3=3>>3
So for the store is 28*.5=14>>14
Comen has 250-60= the car
#### 5

The entrand? combined the nails, Prealk some sitting turtles flooses to his communker value half of his fet of gold Bob.
#### 5

A distribute d in Franc spends on her anagrus gets for one duj = collection. If Kelory has 100 total doments is a wash whrels have to Durn up and ate 300 feet 
```

foil6 as written, key stream 2, two agreeing draws (400 bytes, prompt 2.557 bits a byte; "John" 0x)
```text
The number of minks, we get 6/2 = <<6/2=3>>3
#### 6

Every picked is tooding corn. They are three times as many blue as old as the number of still one-hole while Sarah has to sell a 20 bananas and Polly has 18. If Michael has already has 20 sweets of his movient and Matel is twice as the number of drew when he gets a solish his shopport, how old will it take for the both have left?
The number of b
```

foil6 as written, key stream 3, one draw (402 bytes, prompt 2.557 bits a byte; "John" 0x)
```text
When Michael: 1 meen mill * 2 = <<2*2=4>>4 miles.
Since the restaurtle takes 4 mages by 3 hours, and 20 minutes is 80 8 * 12/100 = <<4200*18=210>>27 boxes of cheese pizzas.
Jack scores, Caven, Novia divided from the same amount of while Cothey is on, calculate the rest of the be turtle of the cattle son will be Ale's 3 slices.
There are 300 feet/student, then company will by the furtles visited for 
```

foil6 as written, key stream 3, two agreeing draws (402 bytes, prompt 2.557 bits a byte; "John" 0x)
```text
First find the number of people on the week
Then find the number of sweets
Then find the total number of square feet by multiplying the two hours
Then find the total number of pickets
Then find the total number of hours she spends by the number of sweeks by the number of calories per hour: 20 x 4 = <<20*4=100>>100.
The school has 300 + 200 = <<200+200=200>>200.
The total number of people are now is 
```

foil6 as written, key stream 4, one draw (401 bytes, prompt 2.557 bits a byte; "John" 0x)
```text
5 x 24 - 5 = <<60-85=45>>43 paces
Together they divided 75 years + 40 colors = <<19+15+9=11>>2 .
Then she will be 3+28 = <<13+2=13>>13 points.
#### 13

Egen has 400 watches for the flurtle and Ivath saves spent $7. How much does Chelony use?
Tom take to all the Tamolioriales 4 x 2 = <<6*2=48>>264 minutes.
Mary has 150 x 1/4 = <<150*1/4=30>>650 stogers is a hirt.
The athale must will take 500 - 3 = 
```

foil6 as written, key stream 4, two agreeing draws (401 bytes, prompt 2.557 bits a byte; "John" 0x)
```text
The total number of stills Julie's tries to find the total number of beads per hour.
#### 5

As in the first stushroom is hop for the bread of what is the average of free time, in scored was down and half of the reed of minitial in both parts and each bank is home with a clothes to make a changle and he has 3 points. If Kation is $400 and he treat, how much does he have now?
Lake is $20 x 4 = $<<20
```

foil6 as written, key stream 5, one draw (404 bytes, prompt 2.557 bits a byte; "John" 0x)
```text
There are just and $0.5*6 = $65.00
So the third total of 50+6/2=$<<
#### 3

Gaine  scored inclimes.  How much does Julaury: 6 Wills.  The femeliys toin remaining watermen length of 2 feet, how much will the second end of the car needs?
Kanie has 3 pounds of 10+6 = <<8*9=7>>5.
Mark had ,000+150 mander that she needs to make a she.
Let, then times in 200 - 160 = <<200-90=263>>2600 dollars.
He does less 
```

foil6 as written, key stream 5, two agreeing draws (402 bytes, prompt 2.557 bits a byte; "John" 0x)
```text
The total distance together the first hour is 50*15=<<15*10=50>>50 more seam
200 x 500 = <<100*.25=50>>50 miles per hour.
#### 50

A costs $1.50. The mill is $0 in each, how much did Mark have left after he need to a coffee in a ball if the picket?
The total cost of $400 x $3000 + $6000 + $3000 + $4000 + $3000 + $3000 + $80 = $3000 in a week.
#### 260,000

Tom has to sell a $20 before school is $20 
```

foil6 as written, key stream 6, one draw (402 bytes, prompt 2.557 bits a byte; "John" 0x)
```text
Stef Jan reads 2 + 6/60 = <<80/8=7>>7 kg commuto cats
On the third  times the grouts 10 years it disent in C=xparts left after a total after time by 
Durd's collection with 6 / 3 = <<6/3=7>>more in one kg
So the heam train leased 5*5=3itial number of speed year
#### 5

Team what's the number this trips sandwich and 10 people den and Simum haven bally costs 40/7 ÷ 5 hours = <<30/2=6>>6 hours
If the 
```

foil6 as written, key stream 6, two agreeing draws (402 bytes, prompt 2.557 bits a byte; "John" 0x)
```text
First find the number of bottles of fruit: 3*.5=<<2*.5=3>>3
Then add the time she spends by the number of stills by the number of sead by the number of seam is 300+30 = <<200+150=180>>140
Total stars will each have a total of 80+120 + 6 = <<60+120+60+120+240=545>>45 more thirds to get der
#### 280

A is two weeks, Tom is currently aid they save $32 each. If Amen has 4 years old as a rate of $50 per 
```

foil6 as written, key stream 7, one draw (400 bytes, prompt 2.557 bits a byte; "John" 0x)
```text
Each week those 108 + 100/3 = <<70/3=45>>45 hours
The purchases are sweet onion-11 square udients because 14 - 3/4/10 = <<90/0.0=.70>>75.
The farm mcan drinks 36 packs of the weight, the eltherine had 106/2 = <<14/2=3>>3
Then find the recorders produces down pizz school and little team choes at the will be $5.00 more x .65 = <<100*.5=25>>25 dollars.
She has a sitracting the salk was 60-12-20=$<<24
```

foil6 as written, key stream 7, two agreeing draws (402 bytes, prompt 2.557 bits a byte; "John" 0x)
```text
The new is twice as many snails as Julia and 3 times as many hours per hour as he has 3*1.5=<<6*.5=16>>16.
The first-thirds is 2 * 2 = <<3*2=8>>8 miles per hour.
Thus, we get 2*2= <<2*3=6>>6 dollars.
The sum of school is 80*.8=<<12*.5=15>>15 feet
#### 5

Tom has a pril.  The second students, he has $300 for $300 each, how much does he spend on a large initial for the other is left after he have left
```

foil6 as written, key stream 8, one draw (402 bytes, prompt 2.557 bits a byte; "John" 0x)
```text
To weet, the dogs is 1/2*5 = <<2*(2*5=5>>5 minutes to find the total amount: 4D times is 50 x 50 = <<50*50=90>>90
He goes would add this paid 20*40 + 20 = <<600+20=1300>>1700 studies
Then he has left
So the decakor is 160/10=32
Then add the glasses left: 6 less express in’s scored 60 / (.6/10 = <<60/10=25>>25 dollars.
Nys now, there * 4 = <<5*4=20>>20-5During on.
#### 0

There are by 7 boys, how m
```

foil6 as written, key stream 8, two agreeing draws (406 bytes, prompt 2.557 bits a byte; "John" 0x)
```text
There are 5*2 = <<2*2=4>>4
Then add the number of male is two turtles
This means the number of white cires is 60 + 12 = <<60+12=120>>120 minutes
#### 80

Trey has 3 years old squiral $2, and planted 90 cars each. The percentage of his friends is a homebruient. What is the total time by multiplying the number of kg of his new cows for the teament to find how many sweets are left by the weight: 30 people 
```

---

## Report: pass7

PC run, pass 7 (fourth and last of the amended-key passes)

Reading: no sample names John. As written 0 of 16, framed 0 of 16, foil7 0 of 16. No "volunteer", "shelter" or 72 anywhere. The prompt codes at 2.716 bits a byte as written and 2.057 framed; foil7 codes it at 2.598.

Held-out: bankA7 1.598 bits a byte (bankA6 1.599); foil7 1.774 (foil6 1.785).

bankA7's peak resident set rose to 465,924 KiB, against about 383,000 KiB on each earlier banked pass. In foil7, key stream 6, one draw, the "�" is a raw 0xA3 byte, a stray UTF-8 continuation byte the tower released.

## Pass 7: amended key (29b76d727), banked bankA7, bankless foil foil7

**bankA7**: PROJECTION 1311 x 159.3 ms + 4.48 s = 213.3 s (159.3 ms: the largest window measured on the amended key, bankA6's pass beside foil6; 4.48 s the largest held-out read, devK_bank); DEADLINE 214 s (runner timer and outer timeout); early stop when the mean section time passes 159.3 ms; RAYON_NUM_THREADS=8, beside foil7
measured: wall 183.4 s (0.86 of the projection), peak resident set 465924 KiB; `RUN_RECEIPT exit=0 wall_s=183.4 peak_rss_kib=465924 user_s=1225.5 stopped=no`; windows 119.8–157.6 ms, mean 136.2
`TOWER_PASS pass=0 train_bits_a_byte=1.532 dev_bits_a_byte=1.598 dev_regions Q=1.801 P=1.339 N=2.304 M=1.197 deposits=1311/1311 pass_ms=182947 elapsed_ms=182976`
state bankA7/STATE sha256 1dee7db05633e773c7b9e4e0eda6db1ab54bce979a4014e0a696f35adeb56ea4

**foil7**: PROJECTION 1311 x 79.4 ms + 3.11 s = 107.2 s (79.4 ms: the largest window measured on the bankless law, foil4's pass beside bank4; foil6's windows ran 70.9-73.1; 3.11 s the largest held-out read, foil4); DEADLINE 108 s (runner timer and outer timeout); early stop when the mean section time passes 79.4 ms; RAYON_NUM_THREADS=8, beside bankA7
measured: wall 98.3 s (0.92 of the projection), peak resident set 234384 KiB; `RUN_RECEIPT exit=0 wall_s=98.3 peak_rss_kib=234384 user_s=578.2 stopped=no`; windows 71.4–73.5 ms, mean 72.4
`TOWER_PASS pass=0 train_bits_a_byte=1.721 dev_bits_a_byte=1.774 dev_regions Q=1.879 P=1.674 N=2.381 M=1.190 deposits=1311/1311 pass_ms=97811 elapsed_ms=97838`
state foil7/STATE sha256 6ec58f70e848d81ba841d0fbe639f374f641c656f4617970e8159b3cbb132395

### bankA7, prompt as written: 0 of 16 samples name John

bankA7 as written, key stream 1, one draw (400 bytes, prompt 2.716 bits a byte; "John" 0x)
```text
Tabby will have been she writed for 7 - 2 = <<7+2=6>>6 hours
#### 2

Lilary was  one basm tijo their sacce were enough and this amount from the combined.  He drinks and 5 hours did opean?
C=<<8+5=5>>5 years.
Timbie used a total of 5*6=<<10+8=16>>16 games.
Sigh, Basis after two know is 24 x 2*4 = <<24*4=200>>200.
He buys four dow/3 calculatings, Hiranny is /2 = <<8/2=6>>6 gird ticks.
The number of 
```

bankA7 as written, key stream 1, two agreeing draws (400 bytes, prompt 2.716 bits a byte; "John" 0x)
```text
There are a total of 2 * 3 = <<2*3=6>>6 years old.
#### 6

An a speed is 5 years old.  How many dollars does he have in?
Michael has 6 - 5 = <<6-5=8>>8 hours.
The total number of whole that is 8*4 = <<8*4=8>>8 hours.
The total number of hours he has 6/2=<<12/2=6>>6 years old.
So in total, the total number of hours he has 6/2 = <<6/2=8>>8 hours.
The total number of hours he has 6 - 3 = <<6-3=6>>6 t
```

bankA7 as written, key stream 2, one draw (400 bytes, prompt 2.716 bits a byte; "John" 0x)
```text
In the day/ment to the first still + 1 - 5 = <<1+3+10-3=2>>2 years old fracus 
#### 1

Durant has 20 people who is weekg them to sell 3 times A meach weigh3 and Moyee and suck subbest in 2 basket that amount of his old valant and every time, she has his dother. If 5% of the plangs wage?
If Sony is 3/5 times as many people as the number of adults of the half-6-6 hours/hour/day/week because 2 - 3 = 
```

bankA7 as written, key stream 2, two agreeing draws (402 bytes, prompt 2.716 bits a byte; "John" 0x)
```text
He has 3*100=<<2*60=80>>80
Then find the time he has to find the time he had by the number of second to find how many peaches total number of second times: 200 - 200 = <<200-40=300>>300 stills
Then find the time he has to find the time he has to find the time he has to find the time he has to find the time he has to find the time he has to find the time he has to find the time he has to find the tim
```

bankA7 as written, key stream 3, one draw (400 bytes, prompt 2.716 bits a byte; "John" 0x)
```text
Each month, there are 80 notbs - 6
Then find the total number of cookies James spends onto the total: 60 x 3 = <<40*3=2*100>>2day, 20*4 * 5 = <<20*5=120>>120 foots
Then subtract the weight Carla droper: 40 – 7/4 = <<60-15-econds is * 3 = <<60+3=50>>50 cents
Since Chryillar has 400 apples’s toger: 4 miles / 9 + 3 = <<60+3=90>>3 the first one clow.
Ever that means the d walk which were 30 + 3 = 
```

bankA7 as written, key stream 3, two agreeing draws (400 bytes, prompt 2.716 bits a byte; "John" 0x)
```text
First find the total number of gold : 4*.m=
Then find the total number of gold value by multiplying the cost for the price by $.5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 x .5 
```

bankA7 as written, key stream 4, one draw (400 bytes, prompt 2.716 bits a byte; "John" 0x)
```text
If Nain have pies
Then find the number of tents prived 12*.4 = <<24*4=20>>20 mother cookies
x, Jase fined number of minutes Redic originally.
#### 3*40=40>>4 birt cructs
Vano is 5 students, they went 10 + 8 = <<60+5+8=32>>32 weeks.
Thus, Michael spractives are 9 playing week, a total of 4*1=<<6*1=68>>6 times
#### 18

Aleger’s wanning is himume every both his brother. How many will have two head 
```

bankA7 as written, key stream 4, two agreeing draws (404 bytes, prompt 2.716 bits a byte; "John" 0x)
```text
The total amount she has 15 * 3% = <<.2*.5=6>>6 years old.
The total amount she has already has 15 * 3 = <<15*3=45>>45
The total amount of money Sam is $45 x 3 = $<<3*3=35>>35.
#### 35

Michael has to save up a day, it will pay up at $50. How much did he have to get?
The total amount of money she has to find the total amount of money she has to find the total amount of money she has to find the total 
```

bankA7 as written, key stream 5, one draw (403 bytes, prompt 2.716 bits a byte; "John" 0x)
```text
The tipp that re-fifths/hour
20 * 4 = <<60*4=100>>100
The number of cookies is 100+% = <<100*4=200>>20
There are 5*4 = 240 / 300 =(1. hours in the Com is 8*2 = <<8*4=120>>120 gallons
Then divide that amount: 6 days * 3 = 80
Then, the total in monthances it takes 6*3=<<6*3=54>>54
Then find the sport Ann's animal: 10 years is * 2 = <<20*2=200>>20
#### 40

After 20 lott were 1/2 whole flam incraile the 
```

bankA7 as written, key stream 5, two agreeing draws (402 bytes, prompt 2.716 bits a byte; "John" 0x)
```text
The total distance the birthday: 2 + 12/5 = <<20*5=20>>20 birthday
Then find the total number of Frequial because 80 / 10 = <<60/5=15>>15
Then find the number of taxes: 6 * 3 = <<6*3=6>>6 dollars.
If he should start his clothes: 6 - 6 + 2 = <<36+12+2=3>>3 years old.
The total number of malculate the total number of malks is 6 * 3 = <<3*3=8>>8.
Tom has 12/2 = <<24/2=6>>6 dollars.
After buying servill
```

bankA7 as written, key stream 6, one draw (400 bytes, prompt 2.716 bits a byte; "John" 0x)
```text
Carly:6/4 = <<6/4=1>>1 hours
#### 1

Jamie sells a total foottall on causa caus, and three owner, Michael has Becko less than the first house of his 35 paims. Coppeaches.
The bove ended the next 2 ounce that is 3/8*1.5 cars total. 15-3 skembers for three friends is travels where were 3 the second half and a teasons more timore that the first day, he worked 1 (2 liter ft/day, Jord Dave up.
Since th
```

bankA7 as written, key stream 6, two agreeing draws (402 bytes, prompt 2.716 bits a byte; "John" 0x)
```text
First find the total number of movies: 3 must * 2 = <<6*2=8>>8
Then divide the number of cookies: 16 hours total number of cookies * 2 = <<16*2=6>>6 years old.
So, Mark is 8 - 3 = <<16+3=8>>8
Then find the total number of cookies: 6 years / 3 = <<6/3=6>>6 miles.
#### 6

Grelo has 200 struckfasts to play. The number of cookies are serving time, how many more expens did Michael cookies?
The number of 
```

bankA7 as written, key stream 7, one draw (400 bytes, prompt 2.716 bits a byte; "John" 0x)
```text
So they had 6 hours, which taks 40 + 3
30x + 16-30 = <<60+14+6+24+7*3+16=190>>190
He figurved 12+00 feet * 100 40 = <<100*1000=40000>>30000 discount
#### 2000000

After the weight of resully of whole that Sametty's play spactle teak.  What is the father?
Rachine receives 30 years X = 50
10/60 = <<100/60=300>>300.
If the first 100% of the final distance of applient resully and 3 hours of them off 5
```

bankA7 as written, key stream 7, two agreeing draws (402 bytes, prompt 2.716 bits a byte; "John" 0x)
```text
He gets 6*10=<<2*8=40>>4
The subtract the first day: 50 - 30 = <<100+30-50=20>>20 dollars
#### 20

There were 30 miles and Simum and a full days a full day. How much did she need to reed by bove before the pants does he need to reed by bove before the pants?
If he has 300 dollars / 50 seconds = <<60/4=20>>20 pants.
#### 20

Fantity has 20 pants, for a went for the total number of apples that he has 
```

bankA7 as written, key stream 8, one draw (400 bytes, prompt 2.716 bits a byte; "John" 0x)
```text
Tony rent is a total of 15 x 4 = <<7*4=3>>3 orange has to find the probreaking her fracted of tlance mouds because 1 + 2x = <<15+2=40 s
The total number of baskets can because .60/s/-.2=
Then find the number of basketctok serving total: 6 * 4 = <<12*4=8>>9
#### 8

Mrs. Tom, the children gives a jecd by 2/3 each.   Jill is Mim and was 2 hours for the across mow less than the at ina born weigh?
Co G
```

bankA7 as written, key stream 8, two agreeing draws (409 bytes, prompt 2.716 bits a byte; "John" 0x)
```text
The total number of basks, we find the total number of basks.
Together, the total number of basks, we find Because Jolly is +6
Then find the number of basks.
#### 4

A weekly wanted, Jason has to saw on a duce for every 2 miles per hour.  The school is 2*3-20=<<200*5=100>>100 gold as the total number of baskets.  How much did he make from his fement school?
The total number of baskets, the total number of 
```

### bankA7, prompt framed: 0 of 16 samples name John

bankA7 framed, key stream 1, one draw (407 bytes, prompt 2.057 bits a byte; "John" 0x)
```text
Tadd that will have don travel time by  through the number of watts (worth of Altogether.
The total number of glass+2=
This total number ping: 20 - 8 = <<45-4=8>>8
There are 7-2 = <<10-2=4>>2 discounts
In total the 3, Matt is left in the pretie so takes 30/2 = <<60/2=90>>90 gallons
Then find the number by him 2 hours
Then cat: 4, the sile many cookies bought a total of 3*9 = <<60*1.5=2>>25
Then find the 
```

bankA7 framed, key stream 1, two agreeing draws (401 bytes, prompt 2.057 bits a byte; "John" 0x)
```text
The fourth of the shopping liked by 6/2 = <<6*2=6>>6.
In total, Jimmy ate a total of (2/3)*.6 = <<1/2*6=36>>36 inches.
#### 26

Tam has to make a speed of flight shopping. The total number of movies stead of flight shopping and Michael traveled by 2 pages and Michael traveled by 2 pages per hour.  If Rody has to make a speed of flight shopping amount shopping?
The 5 x 3 = <<100*3=40>>40 minutes.
In
```

bankA7 framed, key stream 2, one draw (401 bytes, prompt 2.057 bits a byte; "John" 0x)
```text
And pofting 50 minutes to find the number of represents we need to find the total number of gifts.
Alfinally, Je's area of C/bun's age * 30/4 = <<100*1504=200>>200
Then Ben needed: 50mother = <<100*2=100>>100 boods
Then add the first addition: 5 episodes * .01 remaining.
The dlake Durback bood12 + 4 times = <<8+4+8=28>>28 more still.
Then half of this tild – 12 - 2 = <<8-2=8>>8 square feet dest.

```

bankA7 framed, key stream 2, two agreeing draws (401 bytes, prompt 2.057 bits a byte; "John" 0x)
```text
He has 3*2=<<2*2=8>>8
#### 5

Tom is going to be an average of his friend. If Carl is going to be an average of his friend, how many hours does Michael's total cost?
The number of apples are reduced for the basket/mph = <<6=2>>2 inches
The first time, Michael is going to find the total number of apples in the basket: 4 * 3 = <<8*3=15>>15.
#### 5

Carl has 300 orizzs. She has 5 years to sell on his 
```

bankA7 framed, key stream 3, one draw (402 bytes, prompt 2.057 bits a byte; "John" 0x)
```text
Each month him has 7 kidd/10 = 
Then find the total number of red has increased by the stay: 40 x 3 = <<40*3=60>>60
He gets to go to the price of volds to find the length at not need to another 5 on the 100g of waterming does fabring servat the six trip to find the total number of hotage number of cookies: 3 feet/shirt-10 = <<8+8=24>>24 items
B = 3 x 3-4 = 12 in inches
#### 9

A seginning of the at 
```

bankA7 framed, key stream 3, two agreeing draws (400 bytes, prompt 2.057 bits a byte; "John" 0x)
```text
First find the total number of picket: 15 x 10 = <<15*10=100>>100
Then find the total number of pickets from the first week: 400 - 250 = <<100-50=100>>100
Then find the difference between Mill: 500 - 200/2 = <<5000/2=100>>100
Then find the number of pickets from the first week: 500 - 200/5 = <<200/5=1000>>100
Then find the number of pickets by the number of pickets of 100
Then find the number of p
```

bankA7 framed, key stream 4, one draw (401 bytes, prompt 2.057 bits a byte; "John" 0x)
```text
If Paula spent ($00 * $100 = $<<5*100=700>>2500
It costs 6 days/days * $40+.6 = $20
Diree together they use thth the digh sical mon butted to get the turted: 2-4=<<10-4=6>>6 cans.
Since Bead are deals in Await to be left after 3 difference years, Jermela had 38 x Bricill + 2-7 = <<2+2+14+2-2+60+10=120>>120 for the total number of hours left after four times the spee
#### 50

A*6 for the namers has 
```

bankA7 framed, key stream 4, two agreeing draws (401 bytes, prompt 2.057 bits a byte; "John" 0x)
```text
The total amount of the pincomes this means there will be 2*80=<<2*80=240>>240
Then find the number of bottles to find the number of bottles in subtracte the total amount of the pincom: 40/2=<<20*2=60>>60 s
Then find the number of bottles in: 20 - 10 sq ft/= <<20-5=20>>20 people in the bottles.
The total amount of the pincomes that are from the pincomes incomes incomes incomes incomes incomes incom
```

bankA7 framed, key stream 5, one draw (400 bytes, prompt 2.057 bits a byte; "John" 0x)
```text
The new person has $.0(60 years (60*0.0=(000
Then find the total amount of time t
Then find the number of pickets.
So for the first day, there are a total of 2*60+16)
Then find the time the C both: Due travel 40 / 3 = <<60/3=100>>100 calors cans of flave to find the total amount of preed: 16 x 4/100 = <<12*.5=40>>250 steil.
Then do the second year, the first.
He need to 35/3 = <<9*3=40>>2
Total: $
```

bankA7 framed, key stream 5, two agreeing draws (401 bytes, prompt 2.057 bits a byte; "John" 0x)
```text
The total distance the birthday, we subtract the number of people in a week
Then find the total distance Meginny: 150 - 10 = <<30-10=30>>30 minutes
Then find the number of people are $3: 60 / .50 = <<60/50=50>>50 minutes
Then find the total distance the number of people are dinning: 20 people - 20 - 20 / .50 = <<1000/50=100>>100
Then find the total distance the number of people are need: 20 - 20 - 
```

bankA7 framed, key stream 6, one draw (401 bytes, prompt 2.057 bits a byte; "John" 0x)
```text
Mr. Meilolun tows 0/12 equals 50 miles more times cream to clean the final left to run to clean the friend turtle and 4 times 20 allows long.
Since Jill's runled (.15(.25)/3*60/number of apples.
Since food costs five weekend is $4/2 = a weekly dome
He dinter that will be 12/2 = <<12/2=8>>8 hours.
In 3 days he was 9*15 britts.
#### 75

Lyra had a sebeach pizza and home one-A ull sets left. How much 
```

bankA7 framed, key stream 6, two agreeing draws (400 bytes, prompt 2.057 bits a byte; "John" 0x)
```text
First find the total number of subtract the number of subtract the number of subtract the number of subtract the number of subtract the number of subtract the number of subtract the number of subtract the number of subtract the number of subtract the number of subtract the number of subtract the number of subtract the number of subtract the number of subtract the number of subtract the number of s
```

bankA7 framed, key stream 7, one draw (400 bytes, prompt 2.057 bits a byte; "John" 0x)
```text
Since Tarbar drives thructer the week so he goes her sister if he gets 0 x 1000 = <<5*1000=32000>>300
Then find the complete's the total number of cookies: milk because 40*4/0.10 = 2000
Then the number of cookies: 20 bask* 3 candy = <<20*6*.05*.01=300>>300.
And spends 4*20 - 100 = 18/500 = <<3000/500=200>>200
March, It gave by 80+1000=$<<200+1000=200>>200
#### 2000

pander has 1,000 perion countlo
```

bankA7 framed, key stream 7, two agreeing draws (404 bytes, prompt 2.057 bits a byte; "John" 0x)
```text
He gets this means he needs to have $12/2 = $400 for the gold now.
In 30 years she has 400 x 2*.6 = $<<200*.6=240>>240
Then subtract the number of still figure out how many pens are not like to find the total number of water: 20 / 3 = <<20/3=10>>10 people in the gold now.
And is equal to 6 * 3 = <<9*3=6>>6 years old.
And is equal to 6 years - 8 x 3 = <<24+2=8>>8.
There are 400 - 8 = <<20-8=2>>2 dollar
```

bankA7 framed, key stream 8, one draw (403 bytes, prompt 2.057 bits a byte; "John" 0x)
```text
Wuel' that is ables/ 25 times = <<3*100/5=50>>50
Therefore, the furant is 40 * 60 porcents = <<60*60*50=120>>120 degred.
Therefore, C box will be 5*200 = <<5*100*75=200000.00>>30,000
Then add the number of cats by the number of cats contribut: 3500 + 30 miles / 2 = 25 minutes.
#### 350

Chpizzie bill is 1000% are flyester to show.  Rushow had 200 kiloment students make a mi to expresent, and.5 dollar
```

bankA7 framed, key stream 8, two agreeing draws (403 bytes, prompt 2.057 bits a byte; "John" 0x)
```text
The total number of family cans Marion is 200 + 6/3 = <<200 + 6/ment the number of people = <<200+6*50=60>>60 minutes
#### 60

Michael has to her sister is abily and Jast year.   40% of them are $600 and he sold to family and he has to spend on a speeping. What is the total time to get to the previous monthly for the previous monthly for the previous monthly for the previous monthly for the previous 
```

### foil7, prompt as written: 0 of 16 samples name John

foil7 as written, key stream 1, one draw (401 bytes, prompt 2.598 bits a byte; "John" 0x)
```text
T12>>12 aparts
x = 12 x 3 = <<16*3=3>>6>>26 less than the number in the daou spent 
This means tome*2x=<<2*5=24>>24 ears
Thirrel's araged each last half-12- points less than plmale is requat won Wil left.
He also has 5 more waterman is the first, there are 2*2=<<2*2=>>3 points
Then divide the enguffed and the second prove jobs one point: 4*.2= <<2*3.2=6>>6 dollars tome.
The cakes, the Rick and has 
```

foil7 as written, key stream 1, two agreeing draws (403 bytes, prompt 2.598 bits a byte; "John" 0x)
```text
There are 2*2=<<2*2=4>>4
#### 2*4=8>>8 people on the birthday for the tead of each month.
After 2 hours, Mily, Michael has 6 / 2 = <<6/2=3>>3 points.
There are 3 * 3 = <<2*3=6>>6 slices of flag and Jason scored 3 miles to get to the game.
Thus, Sue will take 3 * 3 = <<6*3=6>>6 students bring the first.
So, Sub has a total of 28 + 6 + 8 = <<26+8+66+28=26>>26 mortures.
#### 326

Julion has already has 
```

foil7 as written, key stream 2, one draw (401 bytes, prompt 2.598 bits a byte; "John" 0x)
```text
Each of 300/3=<<15/3=5>>5 hours together.
#### 15

Gail have been pen is 45 yards and 5% of 8 ounces of watth both scus. She wants to found trashroom of sealoaves, and. The flealy has 2 servingps have already use the for the number of knives, Nexccore of his basketbooks. Calculate the total number of worments are borrows weigh 30-fifth = 5 narsn't like ter to volummer and paper ticket.
Since Marty 
```

foil7 as written, key stream 2, two agreeing draws (402 bytes, prompt 2.598 bits a byte; "John" 0x)
```text
The number of portions she has is 4 + 6 = <<8+6=28>>28 points.
If Jason has 36 – 6 = <<66-6=18>>18 pieces.
Team scored 28 + 63 + 6 + 36 = <<26+36+66+36+666+66=636 blue apples
#### 236

Toon has 43 hours, and his friends, and Bob has 4 stock and Paul. If he has 80 packs of his friends, how many minutes does he have in the new have now?
Tom has 40 + 28 = <<70+45=40>>40 per hour.
The total number of 
```

foil7 as written, key stream 3, one draw (401 bytes, prompt 2.598 bits a byte; "John" 0x)
```text
Carlos gave a 7 kid=<<7*(5=20>>20 speels
Then find the difference, she now has left: 6 × 6 = <<2*6=30>>30 on corn
Then find the total number of knives: 10 carries * 10 moresses = <<2*10=20>>20 miles in the housing game in the ched now.
#### 30

She sold at 24 hours on Thursday. If in tries Mark locats A-fleased twice the number of brother ropers at the Green hom, how many can eat did his message?

```

foil7 as written, key stream 3, two agreeing draws (401 bytes, prompt 2.598 bits a byte; "John" 0x)
```text
First find the number of people on the week
Then find the number of sweets
Then find the total number of square feet by multiplying the total number of eggs by the number of sweets left: 50 people * 1000 people = <<1000*.20=80>>80 calories
Then find the total number of cats by the total number of initial number of gavored sweet: 1000 - 2000 = <<1000-2000=100>>100 gards in the femalon.
The second fl
```

foil7 as written, key stream 4, one draw (401 bytes, prompt 2.598 bits a byte; "John" 0x)
```text
The total length of the saby payer to find the orelia hok per hour: 28 packs + 40 years = <<50+60=55>>50
#### 50

Then subtracting the bagcer wheed Lmita gives hen this week.  Together, the factory is 1000 miles / 5 bead which scores total. If it takes 30 minutes, how many puppies can There were 5 for the day because 5 balls are groups have per year, the sysevalance cover student to find the total 
```

foil7 as written, key stream 4, two agreeing draws (402 bytes, prompt 2.598 bits a byte; "John" 0x)
```text
The total number of stills Julie's agos: 2 * 7 = <<2*5=2>>2 years old.
So, he has 25 + 3 = <<2+3=5>>5
#### 5

Carole has 3 miles per hour. The total number of streets as old as the number of polds and Amy women is 40-30 minutes each. If Carole has been scored up a total of 3 * 3 = <<2*3=6>>6 peaches.
To has 20 sweets + 2 * 2 = <<2*2=8>>8 mushrooms left.
On the third day, he has 60 minutes - 60 minut
```

foil7 as written, key stream 5, one draw (400 bytes, prompt 2.598 bits a byte; "John" 0x)
```text
The totalgrades are $0.5*X = 
There were 6 bons - 11 each = 12-2x=
#### 2

Great, how many still does Carloaden, for 26 muture by 2 minutes in a job?
Grip bought / 3 = <<3=3>>3 points.
#### 6

Tom has one between a bread than Faround and Bs.
So he has 4/5 = <<6/5=1>>1 hour in the red years old.
#### 3

Toon has two lizites, 7 maler labed. He has 20 gallons of feed the father uncycler tread goated 
```

foil7 as written, key stream 5, two agreeing draws (401 bytes, prompt 2.598 bits a byte; "John" 0x)
```text
The total distance together the first hour is 50+40 = <<10+10=40>>40 minutes
Then he has to find the number of steams per hour: 600 calories * 6000 beas,2000 square feet per hour
The total number of people in the first month is 160 / 3 = <<120/1000=20>>20 years from now.
For 2/3*2000 = <<2/3*1000/100=20>>20 years ago
The total number of hours did on 10+2=<<30+2=30>>30 pounds
Then add the number of 
```

foil7 as written, key stream 6, one draw (400 bytes, prompt 2.598 bits a byte; "John" 0x)
```text
girines 3*3=30 minutes in 1 hour.
She has 6 years – 30 inches = <<10=10>>10 people left over.
6 from scored 3 bab purtles, Sammised a total of 6 + 6 - 3 = <<6+6=22>>26 kepsworks every each week.
So, the number of cheese marinters than the kird, spoub has 3*2 =  tdegrees two posts are from the first day.
After two sions kimprocrows and she gave 3+6= <<7+6=13>>13 points.
So the dist� distance tran
```

foil7 as written, key stream 6, two agreeing draws (400 bytes, prompt 2.598 bits a byte; "John" 0x)
```text
First find the number of bottles of fruit by the number of bottles of flag: 30 years / 3 = <<30/3=5>>5 hours
#### 5

Michael has 20 more than Jack. If Martha has 50 and he needs to seats 1 books, how many people women has there are three times as many people in the second wash?
There will be 12+30=<<12+10=40>>40 minutes in the still.
#### 40

Sarah has 10 years ago. There were 1000 minutes to wash
```

foil7 as written, key stream 7, one draw (402 bytes, prompt 2.598 bits a byte; "John" 0x)
```text
In total, there means he now 4*.2 = <<6*2=3>>3
She rolled the started and the doors cost $7*$.5=$<<.5=3>>3.
Cartalary CDana is Xaviot because 30 x .8 = <<2*5.00=3.00>>3.00
#### 3

Josh gets thflip to spend a playles. The length of the initial flowers costs $300 worth of miles. Zachary receives 30 years againer gouts his new ale if she have works to drolds she is fries for 10 miles and vestnent.  If 
```

foil7 as written, key stream 7, two agreeing draws (403 bytes, prompt 2.598 bits a byte; "John" 0x)
```text
The first year, we get 25+6 = <<15+6=60>>60 minutes
Then divide the amount by the number of polds to find the number of birds how many minutes did Green spend?
There are 40/2=<<80/2=5>>5
Then find the difference between the ale needs to find the total number of new number of people on the bus in the club?
Combine like termelon because we find the total number of square feet by multiply the number of 
```

foil7 as written, key stream 8, one draw (401 bytes, prompt 2.598 bits a byte; "John" 0x)
```text
To * 3.5 = <<4*7=16>>16
Bens: may $6 peterms per day.
All selling the km, the ratching with 23-2=<<27-2=48>>48.
Sue costs 120*$20 = <<4*120=240>>240 opens.
#### 240

Eastor election that is two hours in one he sabycheese with each receive practors are hungring up.   Lorno is 6 - 160 miles in a day, bating contain 500 hours less than the school is 220% * 6000 % = 4 with her stepteast. Alice were job
```

foil7 as written, key stream 8, two agreeing draws (400 bytes, prompt 2.598 bits a byte; "John" 0x)
```text
There are 5*3 = <<2*3=6>>6 cookies
To season's 2-6 = <<2-6=8>>8
#### 6

A cycles is 20 more than the mom is 12 feet, and pole of maximum gushrooms. A is 3 times as many bananas as old as Tom has to drive her mother and 20 minutes for 8 hours. What is the total time by multiplying the number of messores to find the number of turtles of the pickets?
There are 50+50=<<150+10=50>>50 people got
#### 50
```

---

## Report: end

PC run, end: four amended-key passes, side by side

Answer: no. In 128 banked samples (64 as written, 64 framed) and 64 foil samples, none answers about John. None contains "volunteer" or 72. John appears four times, and none is the volunteering question:
- bankA4, framed: a looping new question, "John has already has already…".
- bankA5, framed: "…John spends the ceen a year." inside an answer line. Beside it, a "For a shelter, a shelter…" loop, the only time the prompt's noun appears.
- bankA6, framed: a new question, "John eats 1/6 as much…".
- foil5: a new question, "John has 45 D…".

bankA7 produces none.

TOWER_PASS, all four passes (held-out bits a byte by region):
| pass | tower | train | dev | Q | P | N | M | wall s / projected s |
|---|---|---|---|---|---|---|---|---|
| 4 | bankA4 | 1.629 | 1.610 | 1.820 | 1.350 | 2.299 | 1.186 | 165.2 / 206.2 (alone) |
| 5 | bankA5 | 1.560 | 1.597 | 1.811 | 1.334 | 2.289 | 1.170 | 183.3 / 206.2 |
| 6 | bankA6 | 1.542 | 1.599 | 1.809 | 1.348 | 2.228 | 1.181 | 183.1 / 212.8 |
| 7 | bankA7 | 1.532 | 1.598 | 1.801 | 1.339 | 2.304 | 1.197 | 183.4 / 213.3 |
| 4 | foil4 | 1.787 | 1.822 | 1.909 | 1.708 | 2.511 | 1.351 | 104.2 / 104.6 (earlier run) |
| 5 | foil5 | 1.760 | 1.803 | 1.899 | 1.696 | 2.462 | 1.281 | 98.1 / 107.2 |
| 6 | foil6 | 1.739 | 1.785 | 1.887 | 1.683 | 2.407 | 1.220 | 97.9 / 107.2 |
| 7 | foil7 | 1.721 | 1.774 | 1.879 | 1.674 | 2.381 | 1.190 | 98.3 / 107.2 |

What the passes measure:
1. The banked held-out read is flat after pass 5: 1.610, 1.597, 1.599, 1.598. Over the same passes its training read falls from 1.629 to 1.532, below its held-out read from pass 5 on.
2. The bankless foil keeps falling on both reads (held-out 1.822 to 1.774), so the bank's held-out lead narrows from 0.212 to 0.176 bits a byte.
3. N (the answer numbers) is the banked tower's worst region, and it does not settle: 2.299, 2.289, 2.228, 2.304.
4. The banked tower codes the prompt worse after pass 4, as written 2.224, 2.507, 2.767, 2.716 and framed 1.936, 2.386, 2.225, 2.057. foil4 to foil7 code it at 2.388, 2.670, 2.557, 2.598.

Runs:
- All eight runs completed with every deposit certified (1311/1311) and none stopped.
- Banked peak resident set about 383,000 KiB on passes 4–6 and 465,924 KiB on pass 7; foils 209,948–234,384 KiB.
- Banked largest windows were 143.7, 158.9, 159.3 and 157.6 ms. Each pass's projection used the largest window measured before its launch, and the early stop read the mean (122–136 ms).
- Samples: 2.6 s wall at most, 8 at a time, run between passes so they did not share cores with the measured runs.

State SHA-256s:
- bankA.state fa18c487…6dfa
- bankA4 5f9f9eee…414c
- bankA5 a0e83c88…718d
- bankA6 4b54c9da…9370
- bankA7 1dee7db0…6ea4
- foil5 f266c2e6…ddcf
- foil6 a8139b1c…0e0e
- foil7 6ec58f70…2395

On the PC:
- The bank-john worktree is now detached at 29b76d727, moved from 88737d7e9. It has no tracked changes, and the main checkout is untouched.
- Nothing was committed or pushed.
- The brief's test filter `hnn::tower::bank` selects no tests, because bank.rs has no test module. The eleven are what the filter `bank` selects, and all 11 passed.
