#!/usr/bin/perl
#
use Net::MPD; 
use strict;
use Data::Hexdumper qw(hexdump);
use POSIX;
use Data::Dumper qw(Dumper);
use XML::Simple;
use XML::XPath;
use MP3::Info;
use Scalar::Util qw(looks_like_number);
use IO::Async::Loop;
use IO::Async::Timer::Periodic;
use IO::Async::Future;
use Net::Async::Ping;
use Math::Round qw/nlowmult nhimult/;
use Try::Tiny;
use 5.20.0;
use warnings;

use experimental 'signatures';
my $freestring="";					#freestring is used to select the right loudness profile (e.g. is school tomorrow, then music switches off not too late in the childrens room
my @commandstack;
my @getxpbuffer;
my $savestatepath="/var/lib/mpd/fhemsaves/"; 	# playback states of the MPD instances are saved for each playlist so you dont loose song or audiobook position when changing lists

# the following hash defines all commands that are accepted via the TCP socket. each command gets a function by reference to call via "ref"
# args says how many arguments are needed for the function
# needsonline means that a client needs to be online before the function is executed. in such case the command is queued until the client is online

my $actions = {"detach" => {"ref" => \&detach_slave, "args" => 1},
			   "attach" =>  {"ref" => \&attach_slave, "args" => 2,"switchon" => 1,"needonline" => [2],"replace" => 2},
			   "control" =>  {"ref" => \&control, "args" => 2,"replace" => 0},
			   "setmode" => {"ref" => \&mpd_setmode, "args" => 2},
			   "play" => {"ref" => \&mpd_play, "args" => 1,"switchon" => 1, "needonline" => [1]},
			   "pause" => {"ref" => \&mpd_pause, "args" => 1,"needonline" => [1]},
			   "stop" => {"ref" => \&mpd_stop, "args" => 1},
			   "number" =>  {"ref" => \&musik_number, "args" => 2,"needonline" => [1]},
			   "song" =>  {"ref" => \&musik_song, "args" => 2,"needonline" => [1]},
			   "seek" => {"ref" => \&musik_seek, "args" => 2,"needonline" => [1]},
			   "songakt" => {"ref" => \&musik_songakt, "args" => 1,"needonline" => [1]},
			   "playlist" => {"ref" => \&musik_playlist, "args" => 2,"needonline" => [1]},
			   "savestate" => {"ref" => \&musik_savestate, "args" => 2,"needonline" => [1]},
			   "stateload" => {"ref" => \&musik_stateload, "args" => 2,"needonline" => [1]},
			   "freestring" => {"ref" => \&freestring, "args" => 1,"replace" => 0},
			   "setvol" => {"ref" => \&setvol, "args" => 2,"needonline" => [1]},
			   "switchon" => {"ref" => \&switchon, "args" => 1},
			   "switchoff" => {"ref" => \&switchoff, "args" => 1},
			   "getvol" => {"ref" => \&getvol, "args" => 1}};

# definition of the known hosts. 	   
my @hosts=("kueche","merle","nele","wohn","schlaf","keller");
# the mpd ports for the associated MPD instances. I run all of those instances on my server managed my systemd independent from this app.
my @mpdports=(6600,6601,6602,6603,6604,6605);

my $hosts;

# the following hash gives the parameters for each host. kind of redundant with the information before. To be cleand up. 
# it defines switchon and switchon commands for each client, as those can be different depending on type of system / hardware used
# e.g. the client "kueche" is contrrolled with the fhem device kuechemusik and therefore the app just fires this command to FHEM.
# the numbers for "zuhoeren" "control" etc. are numbers of mp3 files with prerecorded speech output. In those mp3s the device name is mentioned so they are different for each device.
# sinkmach is a regexp used to find the correct sink module for the client using pactl command
# startvol is the initial volume that is set once a client comes online
# "laut" array is used to give the numerical values for different loudness levels. They differ for each device due to the USB sound cards used. With those value the loudness can be changed in a linear way.
# limits controls the times when it is allowed to use a client and with what maximum loudness. It uses the syntax known in FHEM for temperature control

my $i_hosts={"kueche" => {ip => "192.168.2.29", "port"=>6600, 
					"switchoncommand" => "echo \"set kuechemusik on\" | nc neptun 7072", 
					"switchoffcommand" => "echo \"set kuechemusik off\" | nc neptun 7072",
					"zuhoeren" => "032",
					"control" => "085","controlled" => "086",
					"sinkmatch"=>"usb","startvol" => 6, "laut"=> [0,35,39,48,53,60,88,100]},
		   "merle" => {ip => "192.168.2.20","port"=>6601,
				"switchoncommand" => "echo \"{merleon();;}\" | nc neptun 7072",
				"switchoffcommand" => "echo \"set pa_merle desire off\" | nc neptun 7072",
				"zuhoeren" => "031",
				"control" => "083","controlled" => "084",
				"sinkmatch"=>"usb", "laut"=> [0,34,39,45,79,100,120], "limits" =>
							 {"standard" => "06:30 0 20:10 100 24:00 0",
							  "free"	 => "06:30 0 21:30 100 24:00 0",
							  "beforefree" => "06:30 0 08:00 100 21:30 100 24:00 0",
							  "beforeschool" => "06:30 0 21:40 100 24:00 0"}},
		   "nele" => {ip => "192.168.2.17","port"=>6602,
				"switchoncommand" => "echo \"set pa_nele desire on\" | nc neptun 7072",
				"switchoffcommand" => "echo \"set pa_nele desire off\" | nc neptun 7072",
				"zuhoeren" => "030",
				"control" => "081","controlled" => "082",
				"startvol" => 4,"laut" => [0,30,40,48,57,65,70,77,85,,92,100,110,120],  "limits" =>
							 {#"standard" =>  "24:00 0",
							  "standard" => "06:30 0 08:00 40 18:00 120 19:00 70 20:00 65 20:30 57 21:20 40 21:30 30 24:00 0",
							  "free"	 => "06:30 0 08:00 40 09:00 57 20:00 120 21:00 65 21:30 57 22:00 40 22:30 30 24:00 0",
							  #"free" => "24:00 0",
							  #"beforefree"  => "24:00 0",
							  "beforefree" => "06:30 0 08:00 40 20:00 120 21:00 65 21:30 57 22:00 40 22:30 30 24:00 0",
							  #"beforeschool"  => "24:00 0"}},
							  "beforeschool" => "06:30 0 08:00 40 09:00 57 18:00 120 19:00 70 20:00 65 20:30 57 21:20 40 21:30 30 24:00 0"}},
		   "wohn" => {ip => "192.168.2.6","port"=>6603, "zuhoeren" => "033", "control" => "087","controlled" => "088"},
		   "schlaf" => {ip => "192.168.2.5","port"=>6604, "zuhoeren" => "035", "control" => "091","controlled" => "092",
					"switchoncommand" => "echo \"set paschlaf desire on\" | nc neptun 7072", 
					"switchoffcommand" => "echo \"set paschlaf desire off\" | nc neptun 7072"},
		   "keller" => {ip => "192.168.2.18","port"=>6605,"sinkmatch"=>"usb","zuhoeren" => "034", "control" => "089","controlled" => "090"},
		   "neptun" => {ip => "192.168.2.2","port"=>6606,"sinkmatch"=>"usb", "control" => "001"}};

my $path="/data/misc/pa/";
my $hostfile="online";

# the following are regexes to find out about some values out of the pactl command for the different module types. 
my $getpapatterns = {"modules" => 
					  {"reg" => qr/Module #(\d+)/,
					   "name" => qr/Name: (.*)/, 
					   "argument" => qr/Argument: (.*)/},
					 "sinks" =>
					  {"reg" => qr/Sink #(\d+)/,
					   "state" => qr/State: (.*)/,
					   "name" => qr/Name: (.*)/,
					   "volume" => qr/^Volume: front-left:.*\s(\d+)%/,
					   "mute" => qr/Mute: (.*)/,
					   "slaves" => qr/slaves = \"(.*)\"/,
					   "owner" => qr/Owner Module: (\d+)/},
					 "clients" =>
					  {"reg" => qr/Client #(\d+)/,
					   "pid" => qr/application\.process\.id = "(.*)"/,
					   "owner" => qr/Owner Module: (\d+)/},
					 "sources" =>
					  {"reg" => qr/Source #(\d+)/},
					 "sinkinputs" =>
					  {"reg" => qr/Sink Input #(\d+)/,
					   "sink" => qr/Sink: (.*)/,
					   "client" => qr/Client: (.*)/,
					   "volume" => qr/^Volume: front-left:.*\s(\d+)%/,
					   "mute" => qr/Mute: (.*)/,
					   "owner" => qr/Owner Module: (\d+)/}};
	
my $masterpa;
my $xml;
my $xp;


mpd_connect();	
my $loop = IO::Async::Loop->new;

# open a tcp socket and listen to commands on it. in the function when a command is received it is given to the _cmd function where it will be handled.
my $server = $loop->listen(
   host => '0.0.0.0',
   socktype => 'stream',
   service => 9933,
   on_stream => sub ($stream) {
			$stream->configure(on_read => sub ($self, $buffref, $eof) {
				my $cmd=$$buffref;
				#$self->write(_cmd($cmd));
				#cmd=~s/[0-9a-zA-Z]//;
				#my @args=split / /,$cmd;
				#print Dumper(@args);
				$cmd=~ s/\x0d{0,1}\x0a\Z//s;
				print $cmd;
				_cmd($cmd);
	#			$self->write(_cmd($cmd));				
				$$buffref = '';
				0
			},
		);
      $loop->add( $stream );
   },
   on_resolve_error => sub { die "Cannot resolve - $_[1]\n"; },
   on_listen_error => sub { die "Cannot listen - $_[1]\n"; },
   on_listen => sub ($s) {
      warn "listening on: " . $s->sockhost . ':' . $s->sockport . "\n";
   },
);


# call the mainloop each second. this needs heavy rework.   
my $maintimer = IO::Async::Timer::Periodic->new(
   interval => 1,
   first_interval => 2,
   on_tick => sub { _mainloop(); },
);

$maintimer->start;
$loop->add($maintimer);

# execute pending commands out of the command queue. needs rework. i dont want delay just because the timer is not over yet. 
my $cmdtimer = IO::Async::Timer::Periodic->new(
   interval => 5,
   first_interval => 5,
   on_tick => sub { _executecmd(); },
);

# setup an async pinging to all defined clients. 
my $refreshtimer = IO::Async::Timer::Periodic->new(
   interval => 3,
   first_interval => 3,
   on_tick => sub { _ping();getxp("localhost"); },
);

$refreshtimer->start;
$cmdtimer->start;
$loop->add($cmdtimer);
$loop->add($refreshtimer);
system ("echo \"{check_kalender();;}\" | nc localhost 7072 &");
print "fertig";
# from here on the loop starts and the main program is over. its now all handeled by the mainloop and the other timers.
# i beleive i wont be able to use those async stuff in FHEM so i am trying to understand how to do this in FHEM (waiting for ping, etc.)
$loop->run();



# mainloop checks for all host if they can be pinged, and if yes, tries to read in the status via the pactl command through the getxp function
sub _mainloop{
	my $needprint=0;
	foreach my $host(@hosts){
		if(not defined($hosts->{$host}->{"clientupdated"})){
			ping($host);
			$needprint=2;
			#print Dumper ($hosts->{$host});
		}
		if(not defined ($hosts->{$host}->{"hostupdated"})){
			getxp("localhost");
			$needprint=2;
			#print Dumper ($hosts->{$host});
		}
	}
	if($needprint >1){$needprint--;}
	if($needprint==1){
		##print Dumper($hosts);
		$needprint=0;
	}
	#print Dumper ($hosts->{"nele"});
	#if(!(defined($masterpa))){print "Pulseaudio not running on Neptun\n Exiting.\n";return;}	
}

sub _ping{
	#print "ping..";
	foreach my $host(@hosts){
		ping ($host);
	}
}

# pings a host and based on result updtes the hosts hash with information received
sub ping{
	my $host=$_[0];
	$i_hosts->{$host}->{"mpd"}->ping();
	$i_hosts->{$host}->{"ping"}->{"object"} = Net::Async::Ping->new;
	$i_hosts->{$host}->{"ping"}->{"future"} = $i_hosts->{$host}->{"ping"}->{"object"}->ping($loop, $i_hosts->{$host}->{"ip"});
	$i_hosts->{$host}->{"ping"}->{"future"}->on_done(sub {
		$hosts->{$host}->{"ping"}=1;
		getxp($host);
	});
	$i_hosts->{$host}->{"ping"}->{"future"}->on_fail(sub {
		undef($i_hosts->{$host}->{"hostxp"});
		undef $hosts->{$host}->{"sinkindex"};
		undef $hosts->{$host}->{"clientvolume"};
		undef $hosts->{$host}->{"playstate"};
		undef $hosts->{$host}->{"output"};
		undef $hosts->{$host}->{"online"};
		$hosts->{$host}->{"ping"}=0;
		$hosts->{$host}->{"clientupdated"}=2;
	});
}

# connects to all mpd instances. the app is right now not secure if during runtime some MPD instances fail or are restarted. to be fixed
sub mpd_connect{
	foreach my $host (@hosts){
		try {
			print $host."\n";
			$i_hosts->{$host}->{"mpd"} = Net::MPD->connect("192.168.2.2:".$i_hosts->{"$host"}->{"port"});
		} catch {
			sleep 2;
			warn "MPD connect gescheitert für $host. In 2 Sekunden erneut versuchen";
			mpd_connect();
		}
	}
}

# somehow checks if it is allowed to control another device with a function. i dont understand it myself any more at the time of writing those commants ;)
sub checkreplace{
	my $cmd=$_[0];
	my @args=split / /, $cmd;
	return $cmd if(@args==0 || not defined ($actions->{$args[0]}));
	return $cmd if(defined($actions->{$args[0]}->{"replace"}) && $actions->{$args[0]}->{"replace"} == 0 );
	my $replace=$actions->{$args[0]}->{"replace"} || 1;
	my $host=$args[$replace];
	my $newhost = $hosts->{$host}->{"controlling"} || $host;
	return $cmd if $newhost eq $host;
	$cmd =~s/$host/$newhost/;
	return $cmd;
}

# take control from one client to another and send some audio feedback about this (gongmp3 is a homematic audio device i have in use)
sub control{
	#print "control.. ";
	my $destination=$_[0];
	my $host=$_[1];
	if($destination eq "auto"){
		my $index;
		my $controlling = $hosts->{$host}->{"controlling"} || $host;
		( $index )= grep { $hosts[$_] eq $controlling } 0..$#hosts;
		$index++;
		if($index>=@hosts) {$index=0;}
		$destination=$hosts[$index];
	}
	$hosts->{$host}->{"controlling"}=$destination;
	if (defined($hosts->{$host}->{"online"})){
			my @ansage=($i_hosts->{$destination}->{"control"});
			ansage($host,\@ansage);
	}else{
		system("echo \"set gongmp3 playTone ".$i_hosts->{$destination}->{"control"}."\" | nc neptun 7072 &");
	}
	if (defined($hosts->{$destination}->{"online"})){
			my @ansage=($i_hosts->{$host}->{"controlled"});
			ansage($destination,\@ansage);
	}
	print "\n\nControl: $host kontrolliert jetzt $destination\n";
	return 0;
}	

# function to handle incoming commands. it does some parsing on the incoming text and checks if a command can be executed now or needs to wait until a device is online.
sub _cmd{
	#print "cmd..";
	my $cmd=checkreplace($_[0]);
	my @args=split / /, $cmd;
	print Dumper(@args);
	my $switchonwaiting=0;
	if(@args>0){
		if(defined($actions->{$args[0]})){
			if($actions->{$args[0]}->{"args"} == @args-1){
			    if(defined($actions->{$args[0]}->{"needonline"})){
					my @needed=@{($actions->{$args[0]}->{"needonline"})};
					foreach my $neededhost(@needed){
						if(!defined($hosts->{$args[$neededhost]}->{"online"})){
							if(defined($actions->{$args[0]}->{"switchon"})){
								$switchonwaiting=1;
								if(not defined($i_hosts->{$args[$neededhost]}->{"switchoncmd"})) {
									switchon($args[$neededhost]);
									$i_hosts->{$args[$neededhost]}->{"switchoncmd"}=1;
									$loop->add( IO::Async::Timer::Countdown->new(delay => 150,on_expire => sub { undef($i_hosts->{$args[$neededhost]}->{"switchoncmd"}); })->start());	
								}
							}else{
								return;
							}
						}
					}
					if($switchonwaiting == 1){
						_queuecmd($cmd);
						return;
					}
				}
				_delcmd($cmd);
				if($actions->{$args[0]}->{"args"}==0){
					return $actions->{$args[0]}->{"ref"}->();
				}elsif($actions->{$args[0]}->{"args"}==1){
					return $actions->{$args[0]}->{"ref"}->($args[1]);
				}elsif($actions->{$args[0]}->{"args"}==2){
					return $actions->{$args[0]}->{"ref"}->($args[1],$args[2]);
				}else{
					return "something went wrong\n";
			}	
			}else{
				return "falsche anzahl parameter\n";
			}
		}else{
			return "unbekannter befehl\n";
		}
	}
	return "\n";
}		

# get information about a client and the sinks with pulseaudio pactl
sub get_pa{
	my $result=$_[0];
	my $m;
	my $index;
	my $type;
	my $p=$getpapatterns;
	if(not $result=~/sink/){return "error";}
	my @lines = split /\n/, $result;
	foreach my $line (@lines) {
		$line=~ s/^\s+//;
		foreach my $key (keys $p){
			my $reg=$p->{$key}->{"reg"};
			if($line=~$reg){
				$type=$key;
				#new entry
				$index=$1;
				$m->{$key}->{$index}->{"index"}=$index;
			}
			if(defined($type)){
				my $localhash=$p->{$key};
				foreach my $element (keys $localhash){
					if($element eq "reg"){next;}
					my $temp=$p->{$type}->{$element};
					if(defined($temp) && $line=~$temp){
						$m->{$type}->{$index}->{$element}=$1;
					}
				}
			}
		}
	}
	return $m;
}

# returns the maximum allowed volume for a given host at the current time based on the definition in the limit setting
sub maxvol{
	#print "maxvol..";
	my $host=$_[0];
	my $maxvol;
	my $day=$freestring;
	if(defined($i_hosts->{$host}->{limits})){
		if(!defined($i_hosts->{$host}->{limits}->{$freestring})){
			$day="standard";
		}
		$maxvol=templistdecode($i_hosts->{$host}->{limits}->{$day});
		return $maxvol;
	}else{
		return 200;
	}
}

# this is the full pulseaudio stuff for a host. 
sub getxp{
	#print "getxp..".$_[0];
	my $host=$_[0];
	my $cmd;
	my $process;
	my $result;
	if($host eq "localhost"){
		$cmd = "pactl list";
		foreach my $lhost(@hosts){
			$hosts->{$lhost}->{"hostupdated"}=1;
		}
		$process = IO::Async::Process->new(
			command => $cmd,
			stdout => { into => \$result },
			on_finish => sub {
					$masterpa=get_pa($result);
					if(!defined($masterpa)){return;}
					$xml=XMLout($masterpa);
					$xp=XML::XPath->new( xml => $xml);
					foreach my $xhost(@hosts){
					my $index=sink_index_by_host($xhost);
						if(defined($hosts->{$xhost}->{"online"}) && not (looks_like_number($index)) && not defined ($hosts->{$xhost}->{"tunnelwaiting"})){
							tunnel_load($xhost);
							next;
						}
						$hosts->{$xhost}->{"sinkindex"} = $index;
						if(defined($hosts->{$xhost}->{"tunnelwaiting"})){
							my $maxvol=maxvol($xhost);
							my $startvol=100;
							if(defined($i_hosts->{$xhost}->{"startvol"})){
								$startvol=$i_hosts->{$xhost}->{"startvol"};
							}
							if($maxvol<$startvol){
								$startvol=$maxvol;
							}
							print "setvol wegen tunnelweiting\n";
							setvol($xhost,$startvol);
							undef($hosts->{$xhost}->{"tunnelwaiting"});
						}
						my $index_b=sink_index_by_host($xhost."_b");
						if(looks_like_number($index_b)){
							my @slaves = split ",", $masterpa->{"sinks"}->{$index_b}->{"slaves"};
							my $count=0;
							my $slavescount=@slaves;
							$hosts->{$xhost}->{'slavescount'} = $slavescount;
							foreach my $slave (@slaves){
								$hosts->{$xhost}->{"slaves"}[$count]=$slave;
								$count++;
								if(not defined($hosts->{$slave}->{"online"})){
									$hosts->{$xhost}->{"hostupdated"}=2;
									detach_slave($xhost,$slave);
									return;
								}
							}
							mpd_setmode($xhost,1);
						}else{
							mpd_setmode($xhost,0);
							undef($hosts->{$xhost}->{"slaves"});
						}
						#print "localxpupdate löuaeft\n";
						$hosts->{$xhost}->{"playstate"} = mpd_playstatus_by_host($xhost);
						$hosts->{$xhost}->{'output'} =  mpd_output_by_host($xhost);
						$hosts->{$xhost}->{"hostupdated"}=2;					
					}
			}
		);
	}else{
	     $cmd = "pactl -s $host list"; 
		 $hosts->{$host}->{"clientupdated"}=1;	
		 $process = IO::Async::Process->new(
			command => $cmd,
			stdout => { into => \$result },
			on_finish => sub {
				my $hostpa=get_pa($result);
				### Wenn der HOST nicht online ist dann
				  ## alles auf undef setzen und auch ggf. _b sink löschen
				if((!defined($hostpa)) || $hostpa eq "error"){
					undef($i_hosts->{$host}->{"hostxp"});
					undef($hosts->{$host}->{"online"});
					my $index_b=sink_index_by_host($host."_b");
					if(looks_like_number($index_b)){
						my $mindex=$masterpa->{"sinks"}->{$index_b}->{"owner"};
						mpd_setmode($host,0);
						`/usr/bin/pactl unload-module $mindex &`;
						undef($hosts->{$host}->{"hostupdated"});
					}
					undef $hosts->{$host}->{"sinkindex"};
					undef $hosts->{$host}->{"clientvolume"};
					undef $hosts->{$host}->{"playstate"};
					undef $hosts->{$host}->{"output"};
					$hosts->{$host}->{"clientupdated"}=2;
					return "error";
				}
				$hosts->{$host}->{"online"}=1;
				# hostXP in Hash, Volume überprüfen ggf. neu setzen
				# Falls Host noch keinen Tunnel-Sink hat: erzeugen
					my $hostxml=XMLout($hostpa);
					undef($i_hosts->{$host}->{"hostxp"});
					$i_hosts->{$host}->{"hostxp"}= XML::XPath->new( xml => $hostxml );
					$hosts->{$host}->{"clientvolume"} = getvol($host);
					my $maxvol=maxvol($host);
					if($hosts->{$host}->{"clientvolume"}=~ /^[+-]?\d+$/ and $hosts->{$host}->{"clientvolume"}>$maxvol){
						setvol($host,$maxvol);
					}
				if($maxvol==0){switchoff($host);}
				manage_offtimer($host,"check");
				$hosts->{$host}->{"clientupdated"}=2;
			}
		);
	}
	
	$loop->add($process);
}

# create a new tunnel sink for a new client
sub tunnel_load{
	my $host=$_[0];
	if(defined($hosts->{$host}->{"tunnelwaiting"})){return;}
	$hosts->{$host}->{"tunnelwaiting"}=1;
	`/usr/bin/pactl load-module module-tunnel-sink server=$host sink_name=$host &`;
	undef($hosts->{$host}->{"hostupdated"});
}

# gets the current volume of a client		
sub getvol{
	#print "getvol";
	my $host=$_[0];
	my $hostxp = $i_hosts->{$host}->{"hostxp"} || "error";
	if($hostxp eq "error"){ return $hostxp;}
	my $Volume;
	if(defined($i_hosts->{$host}->{"sinkmatch"})){
		$Volume=$hostxp->find('string(/opt/sinks[contains(@name,"'.$i_hosts->{$host}->{"sinkmatch"}.'")]/@volume)');
	}else{
		$Volume=$hostxp->find('string(/opt/sinks[@index="0"]/@volume)');
	}
	my $retval=eval($Volume);
	if (defined($retval)){return $retval;}else{return "error";}
}

# get the current state of MPD for a client
sub mpd_playstatus_by_host{
	#print "mpd_playstatus_by_host";
	my $host=$_[0];
	my $status=$i_hosts->{$host}->{"mpd"}->update_status();
	my $decoded_status="";
	if($status->{'state'} eq "play"){
		$decoded_status="P";
	}elsif($status->{'state'} eq "pause"){
		$decoded_status="p";
	}elsif($status->{'state'} eq "stop"){
		$decoded_status="S";
	}else{
		$decoded_status="F";
	}
	#print Dumper($status);
	return $decoded_status;
}

# gets the output that MPD is configured to and fixes problems if more than 1 output is enabled accidently
sub mpd_output_by_host{
	#print "mpd_output_by_host..";
	my $host=$_[0];
	my @outputs=$i_hosts->{$host}->{"mpd"}->outputs();
	if($outputs[0]->{'outputenabled'} == $outputs[1]->{'outputenabled'}){
		mpd_setmode($host,0);
	}
	@outputs=$i_hosts->{$host}->{"mpd"}->outputs();
	if($outputs[0]->{'outputenabled'} == 1){
		return 0;
	}else{
		return 1;
	}
	#print Dumper(@outputs);
}

# changes between normal mode and combined mode
sub mpd_setmode{
	#print "mpd_setmode..";
	my $host=$_[0];
	my $mode=$_[1];
	my $playstatus=mpd_playstatus_by_host($host);
	my @outputs=$i_hosts->{$host}->{"mpd"}->outputs();
	if($outputs[$mode]->{'outputenabled'} ==0){
		if($playstatus eq "P"){
			$i_hosts->{$host}->{"mpd"}->pause();
		}
		if($mode==1){
			$i_hosts->{$host}->{"mpd"}->disable_output(0);
			$i_hosts->{$host}->{"mpd"}->enable_output(1);
		}else{
			$i_hosts->{$host}->{"mpd"}->disable_output(1);
			$i_hosts->{$host}->{"mpd"}->enable_output(0);
		}
		if($playstatus eq "P"){
			$i_hosts->{$host}->{"mpd"}->play();
		}	
	}
}

# plays out 1 or more mp3s as audio feedback
sub ansage{
  #print "ansage..";
  my $host=$_[0];
  my @ansage=@{$_[1]};
  my $single=$_[2];
  my $command="cd /data/misc/gong && sox ";
  my $tempname="temp";
  if(scalar @ansage==0 || $ansage[0] eq ""){
	return;
  }
  my @outputs=$i_hosts->{$host}->{"mpd"}->outputs();
  my $sink=$host;
  if($outputs[1]->{'outputenabled'} ==1 && (not defined($single) || $single ne "single")){$sink.="_b";}
  foreach my $element(@ansage){
		$command.=$element."*wav ";
		$tempname.=$element;
  }
  $command.=" $tempname.wav";
  `$command`;
  system("/usr/bin/paplay -d $sink  /data/misc/gong/$tempname.wav &");
}

# used to manage automatic switchoff timers for clients
sub manage_offtimer{
#print "manage_offtimer..";
	my $host=$_[0];
	my $timeout = $_[1] || 10000;
	my $beacon=0;
	if(defined($_[2])){$beacon=$_[2];}
	if(defined($i_hosts->{$host}->{"offtimer"})){
		if(not looks_like_number($timeout)){return;}
		$timeout= ($timeout*60);
		$i_hosts->{$host}->{"offtimer"}->stop();
		$i_hosts->{$host}->{"offtimer"}->configure(delay => $timeout);
		$i_hosts->{$host}->{"offtimer"}->start();
		print "Offtimer $host geändert auf $timeout";
		if(defined($hosts->{$host}->{"slaves"}) && $beacon!=1){
			foreach my $slave(@{$hosts->{$host}->{"slaves"}}){
				if($slave ne $host){manage_offtimer($slave,$timeout/60,1);}
			}
		}
	}else{
		if(not looks_like_number($timeout)){$timeout=(180*60);}else{$timeout*=60;}
		$i_hosts->{$host}->{"offtimer"} =IO::Async::Timer::Countdown->new(
			delay => $timeout,
			on_expire => sub {  switchoff($host);
								undef($i_hosts->{$host}->{"offtimer"});
							 })->start();
		$loop->add($i_hosts->{$host}->{"offtimer"});
		print "Offtimer $host neu auf $timeout";
	}
}

#following functions just do the most basic MPD stuff.
sub mpd_play{
	#print "mpd_play..";
	my $host=$_[0];
	my $status=$i_hosts->{$host}->{"mpd"}->update_status();
	if($status->{"playlistlength"} == 0){
		my @ansage=("055");
		ansage($host,\@ansage);
	}else{
		$i_hosts->{$host}->{"mpd"}->play();
	}
	manage_offtimer($host,180);	
}

sub mpd_pause{
	#print "mpd_pause..";
	my $host=$_[0];
	my $status=$i_hosts->{$host}->{"mpd"}->update_status();
	if($status->{"playlistlength"} == 0 || $status->{'state'} ne "play"){
		send_nack($host);
	}else{
		$i_hosts->{$host}->{"mpd"}->pause();
	}
	manage_offtimer($host,30);
}

sub mpd_stop{
	#print "mpd_stop..";
	my $host=$_[0];
	$i_hosts->{$host}->{"mpd"}->stop();
	manage_offtimer($host,1);
}
	

sub sink_index_by_host{
	if(not defined($xp)){return "error";}
	#print "si_b_host..";
	my $host=$_[0];
	my $index = $xp->find('number(/opt/sinks[@name="'.$host.'"]/@index)');
	if(!(looks_like_number($index))){return "error";}else{return eval($index);}
}

# dettach from another stream *if previously the client was listening to another room
sub detach_slave{
	#print "detachslave..";
	my $dslave=$_[0];
	if($hosts->{$dslave}->{"hostupdated"} != 2){_queuecmd("detach $_[0]");return;}
	undef($hosts->{$dslave}->{"hostupdated"});
	foreach my $host(@hosts){
		my $index_b=sink_index_by_host($host."_b");
		my $match=0;
		my $needb=0;
		my $newslaves="";
		if(looks_like_number($index_b)){
			my @slaves = split ",", $masterpa->{"sinks"}->{$index_b}->{"slaves"};
			my $count=0;
			foreach my $slave (@slaves){
				if($slave eq $dslave){
					$match=1;
					next;
				}
				if($count>0){$newslaves.=","}
				$newslaves.=$slave;
				if($slave ne $host){$needb=1;}
				$count++;
			}
			if($match){
				my $index=sink_index_by_host($host."_b");
				my $mindex=$masterpa->{"sinks"}->{$index}->{"owner"};
				mpd_setmode($host,0);
				`pactl unload-module $mindex`;
				if($needb){
					my $cmd="pactl load-module module-combine-sink sink_name=".$host."_b slaves=$newslaves";
					`$cmd`;
					mpd_setmode($host,1);
				}
				undef($hosts->{$host}->{"hostupdated"});
			}
		}
	}
	manage_offtimer($dslave,1);
}

# audio feedback for a wrong command
sub send_nack{
	my $host=$_[0];
	my @ansage=("055");
	ansage($host,\@ansage);
}

# attach to the next free client, if any
sub attach_find_host{
	#print "attach_find_host ";
	my $host=$_[0];
	my $dslave=$_[1];
	if($host ne "auto"){
		return $host;
	}
	my @online=online_hosts($dslave);
	
	print Dumper(@online);
	if(@online == 0) {return "error";}
	my $master=find_master($dslave);
	my $index=0;
	if ($master ne "error"){
		( $index )= grep { $online[$_] eq $master } 0..$#online;
		$index++;
		if($index>=@online) {$index=0;}
	}
	return $online[$index];
}

# find out to which master a client is listening to
sub find_master{
	my $host=$_[0];
	foreach my $host (@hosts){
		if(defined($hosts->{$host}->{"slaves"})){
			my @slaves=@{$hosts->{$host}->{"slaves"}};
			if (grep {$_ eq $host} @slaves){
				return $host;
			}
		}
	}
	return "error";
}
		


# generate an array of the hosts currently available
sub online_hosts{
	my $slave=$_[0];
	my @rhosts;
	foreach my $host (@hosts){
		my $index=sink_index_by_host($host);
		if($host ne $slave && looks_like_number($index)){
			push @rhosts,$host;
		}
	}
	return @rhosts;
}

## this attaches a specific client to the stream of another client
sub attach_slave{
	#print "attach_slave.:";
	my $dslave=$_[1];
	my $host=attach_find_host($_[0],$dslave);
	if($host eq "error"){
		send_nack($dslave);
		return;
	}
	if($hosts->{$host}->{"hostupdated"} !=2){_queuecmd("attach $_[0] $_[1]");return;}
	manage_offtimer($host,180);
	mpd_stop($dslave);
	detach_slave($dslave);
	if($hosts->{$host}->{"hostupdated"} !=2){_queuecmd("attach $_[0] $_[1]");return;}
	manage_offtimer($dslave,180);
	my $index_b=sink_index_by_host($host."_b");
	my $newslaves="";
	if(looks_like_number($index_b) && getvol($dslave) ne "error"){
		$newslaves=$masterpa->{"sinks"}->{$index_b}->{"slaves"}.",".$dslave;
		my $mindex=$masterpa->{"sinks"}->{$index_b}->{"owner"};
		`pactl unload-module $mindex`;
		my $cmd="pactl load-module module-combine-sink sink_name=".$host."_b slaves=$newslaves";
		my $cmdresult=`$cmd`;
		mpd_setmode($host,1);
		undef($hosts->{$host}->{"hostupdated"});
		return $cmdresult;
	}elsif (getvol($dslave) ne "error"){
		$newslaves=$host.",".$dslave;
		my $cmd="pactl load-module module-combine-sink sink_name=".$host."_b slaves=$newslaves";
		my $cmdresult=`$cmd`;
		mpd_setmode($host,1);
		undef($hosts->{$host}->{"hostupdated"});
		my @ansage=($i_hosts->{$host}->{"zuhoeren"});
		ansage($dslave,\@ansage);
		return $cmdresult;
	}else{
		return "error";
	}
}
# execute the command queue. commands that cannot be executed because a host is not online are added to the queue again by the command itself
sub _executecmd{
	#print "executecmd..";
	for(@commandstack){
		_cmd($_);
	}
}
# add a command to the command queue
sub _queuecmd{
	#print "queuecmd..";
	my $cmd=$_[0];
	if (not (grep {$_ eq $cmd} @commandstack)) {
		push(@commandstack,$cmd);
		$loop->add( IO::Async::Timer::Countdown->new(
			delay => 200,
			on_expire => sub { 	_delcmd($cmd); },
		)->start());
	}
}
#remove a cmd from the queue
sub _delcmd{
	#print "delcmd..";
	my $cmd=$_[0];
	my @dix = grep { $commandstack[$_] eq $cmd } 0..$#commandstack;
	my $o = 0;
	print "deleting...$cmd...found ".@dix." entries\n";
	for (@dix) {
		splice(@commandstack, $_-$o, 1);
		$o++;
	}
}
# switchoff a client by using the predefined switchoncmd
sub switchon{
	#print "switchon..";
	my $host=$_[0];
	if (defined($i_hosts->{$host}->{"switchoncommand"})){
		my $cmd=$i_hosts->{$host}->{"switchoncommand"};
		system("$cmd &");
		print "switch on $host\n"; 
		manage_offtimer($host,180);
	}else{
		print "no switchon cmd defined";
	}
	$i_hosts->{$host}->{"mpd"}->stop();
}

# switchoff a client by using the predefined switchoffcommand
sub switchoff{
	#print "switchoff..";
	my $host=$_[0];
	if (defined($i_hosts->{$host}->{"switchoffcommand"})){
		my $cmd=$i_hosts->{$host}->{"switchoffcommand"};
		system("$cmd &");
		print "switch off $host\n"; 
	}else{
		print "no switchoff cmd defined";
	}
	$i_hosts->{$host}->{"mpd"}->stop();

}

# generate output of a number to a client
sub ansage_num{
	#print "ansage_num..";
	my $host=$_[0];
	my @ar=numberspeech($_[1]);
	ansage($host,\@ar);
}

# generates an array for playback for numbers with a comma and a minus sign (not used here, just copied from fhem where i use it for temerature announcements)
sub minuscommaspeech{
	#print "minuscommaspeech..";
	my $num=$_[0];
	if($num=~/^[0-9]+$/){
		return numberspeech($num);
	}
	if($num=~/^[+-]?([0-9]+)[\.\,]+([0-9]+)/){
		my $gzahl=$1;
		my $nzahl=$2;
		my @speech;
		if($num=~/^-/){
			push @speech,161;
		}
		push @speech,numberspeech($gzahl);
		push @speech,27;
		push @speech,numberspeech($nzahl);
		return @speech;
	}else{
		return "";
	}
}
	
# generate numbers by number snippets prerecorded
sub numberspeech{
	#print "numberspeech..";
	my @einer=("","099", 102, 103, 104, 105, 106, 107, 108, 109);
	my @zehner=("",110,120,130,140,150,160,170,180,190);
	my $hundert="097";
	my $zig="096";
	my $tausend="095";
	my $und="094";
	my $num=$_[0];
	my @speech;
	if($num=~/^[0-9]+$/){
		if(length($num)>4){
			return "";
		}
		if(length($num)>3){
			push(@speech,$einer[substr($num,0,1)]);
			push(@speech,$tausend);
			$num=~s/^[0-9]//;
		}
		if(length($num)>2){
			push(@speech,$einer[substr($num,0,1)]);
			push(@speech,$hundert);
			$num=~s/^[0-9]//;
		}
		if($num>60){
			if(substr($num,1,1) ne "0"){
				push(@speech,$einer[substr($num,1,1)]);
				push(@speech,$und);
			}
			push(@speech,100+(10*substr($num,0,1)));
		}else{
			push(@speech,100+$num);
		}
		return @speech;
	}else{
		return "";
	}
}


=pod
sub musik_austimer{
	my $host=$_[0];
	my $seconds=musik_getseconds($host);
	my $percent=musik_getpercent($host);
	my $remaining = -1*(($percent-100)/100)*$seconds;
	my $offtimer=$value{$host."music_offtimer"};
	if(defined($i_hosts->{$host}->{"offtimer"})){
		$loop->remove($i_hosts->{$host}->{"offtimer"});
		undef($i_hosts->{$host}->{"offtimer"});
	}
	$offtimer=~s/Next\: //;
	$offtimer=abstime2rel($offtimer);
	$offtimer=~/(\d\d):(\d\d):(\d\d)/;
	$offtimer=$1*60+$2+($3/60);
	$remaining = nhimult(1,$remaining/60);
	$offtimer = nhimult(1,$offtimer);
	my @times = ($offtimer, $remaining, 30, 60, 240);
	@times = sort { $a <=> $b } @times;
	my %saw;
	@times = grep(! $saw{$_}++, @times);  
	my $index = firstidx { $_ eq $offtimer } @times;
	$index++;
	$index=$index%@times;
	$offtimer=$times[$index];
	fhem "delete ".$host."music_offtimer";
	fhem "define ".$host."music_offtimer at +".fhemzeit($offtimer*60)." {musik_switchoff(\"$host\");;}";
	my @ansage=(205,numberspeech($offtimer),206);
	ansage($host,\@ansage);
	return $offtimer;
}
=cut

# save the state, used when playlists are changed etc.
sub musik_statesave{
	#print "statesave..";
	my $host=$_[0];
	my $slot=musik_number($host) || $_[1];
	print "Slot: $slot\n";
	my $seconds=musik_getseconds($host);
	my $percent=musik_getpercent($host);
	print "percent $percent\n";
	print "seconds $seconds\n";
	my $elapsed = ($percent/100-0.01)*$seconds;
	if($elapsed<0){$elapsed=0;};
	my $playlist=$hosts->{$host}->{"playlist"};
	if(not looks_like_number($playlist)){$playlist=1;}
	my $tracknumber = musik_getsong($host);
	if(looks_like_number($slot) && $slot==0){
		return 0;
	}
	open OUT, ">".$savestatepath.$host.$slot or return "file error";
	print OUT $playlist."\n";
	print OUT $tracknumber."\n";
	print OUT $elapsed."\n";
	close OUT;
	return $slot;
}

# recover a previously saved state
sub musik_stateload{
	#print "stateload..";
	my $host=$_[0];
	my $slot=musik_number($host) || $_[1];
	if(looks_like_number($slot) && $slot==0){
		$slot="1";
	}
	open IN, "<".$savestatepath.$host.$slot or return "file error";
	my @content=<IN>;
	if(!($slot=~/pl_/)){musik_playlist($host,$content[0]);}
	musik_song($host,$content[1]);
	musik_seek($host,(100*$content[2]/musik_getseconds($host)));
}

# currently i have fhem call the freestring command externaly to the TCP socket whenever the reading in FHEM changes. fhem calculates this based on weekdays and calendar entries for school holidays etc. (using the google calender plugin)
sub freestring{
	#print "freestring..";
	my $arg=$_[0];
	$freestring=$arg;
}

# function called when a client presses a number on the remote. sets a timeout to $last and waits for the next number in case of multi digit numbers.
# numbers are always entered by a client in preperation of a function like next song, next playlist etc.
sub musik_number{
	#print "musik_number..";
	my $host=$_[0];
	my $number=$_[1];
	state %last;
	state %buffer;
	if(!defined($number) || $number eq "" ){
		my $temp=$buffer{$host};
		$buffer{$host}=0;
		if(!defined($temp) || $temp eq ""){$temp=0;}
		return $temp;
	}
	if(time()-$last{$host}>10){
		$buffer{$host}=0;
	}
	$last{$host}=time();
	$buffer{$host}=$buffer{$host}*10;
	$buffer{$host}+=$number;
	ansage_num($host,$buffer{$host});
	return $buffer{$host};
}

# functions "stolen" from the fhem implementation
sub time_str2num($)
{
  my ($str) = @_;
  my @a;
  if($str) {
	@a = split("[T: -]", $str);
	#if(!defined($a[5])){$a[5]=0;}if(!defined($a[4])){$a[4]=0;}if(!defined($a[3])){$a[3]=0;}
    return mktime($a[5],$a[4],$a[3],$a[2],$a[1]-1,$a[0]-1900,0,0,-1);
  } else {
    my ($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst) = localtime(time);
    return mktime($sec, $min, $hour, $mday, $mon, $year, 0, 0, -1);
  }
}
sub
abstime2rel($)
{
  my ($h,$m,$s) = split(":", shift);
  $m = 0 if(!$m);
  $s = 0 if(!$s);
  my $t1 = 3600*$h+60*$m+$s;

  my @now = localtime;
  my $t2 = 3600*$now[2]+60*$now[1]+$now[0];
  my $diff = $t1-$t2;
  $diff += 86400 if($diff <= 0);

  return sprintf("%02d:%02d:%02d", $diff/3600, ($diff/60)%60, $diff%60);
}

# decoder for the FHEM templlist format
sub templistdecode{
	#print "templistdecode..";
	my $templist=$_[0];
	my ($sec, $min, $hour, $mday, $mon, $year, $wday, $yday, $isdst) = localtime(time+86400);
	my $tomorrow=sprintf("%04d",1900+$year)."-".sprintf("%02d",$mon+1)."-".sprintf("%02d",$mday)." ";
	$templist =~ s/^\s+//; # leerzeichen am anfang weg
	$templist =~ s/\s+$//; # leerzeichen am Ende weg
	my @templistelements=split(" ", $templist); # Die Templist in ihre Elemente zerlegen
	my @time;
	my @value;
	# folgende Schleife erzeugt time/value paare aller angegebenen Stellzeiten (geht bestimmt auch viel cooler)
	my $mindiff=time_str2num($tomorrow."23:59:00"); # eine Tageslänge
	my $value;
	for(my $i=0;$i<@templistelements/2;$i++){
		my $diff=abstime2rel($templistelements[$i*2].":00"); # wie lange sind wir weg von der SChaltzeit?
		if(time_str2num($tomorrow.$diff)<$mindiff){$mindiff=time_str2num($tomorrow.$diff);$value=$templistelements[1+($i*2)];} # wir suchen die kleinste relative Zeit
	}
	return $value; # der aktuelle Auto-Wert wird zurückgegeben
}

# creates audio feedback about the current song played 
sub musik_songakt{
	#print "musik_songakt..";
	my $host=$_[0];
	my $pos=musik_getsong($host);
	my @ansage=((208,numberspeech($pos)));
	ansage($host,\@ansage);
	#print Dumper(@ansage);
	return $pos;
}

# get the current song as position in playlist
sub musik_getsong{
	#print "musik_getsong..";
	my $host=$_[0];
	my $song=$i_hosts->{$host}->{"mpd"}->current_song();
	my $s=$song->{"Pos"};
	if(not looks_like_number($s)){return 1;}
	return 1+$s;
}

# change the volume. This is depending onthe volume lookup table. uses pactl to the sink on the client. it also checks if there are limits set. 
sub setvol{
	#print "setvol..".$_[0]." ".$_[1]."\n";
	my $host=$_[0];
	my $step=$_[1];
	if($hosts->{$host}->{"hostupdated"} !=2){_queuecmd("setvol ".$_[0]." ".$_[1]);return;}
	if($hosts->{$host}->{"clientupdated"} !=2){_queuecmd("setvol ".$_[0]." ".$_[1]);return;}
	if(not defined($hosts->{$host}->{"online"})){return;}
	if(not defined($i_hosts->{$host}->{"hostxp"})){return;}
	my $now=time-2;
	if(defined($i_hosts->{$host}->{"lastsetvol"}) && $now < $i_hosts->{$host}->{"lastsetvol"}){return;}
	$i_hosts->{$host}->{"lastsetvol"}=time;
	print "setvol $host $step";
	my $i=0;
	my $ist;
	if(defined($i_hosts->{$host}->{"sinkmatch"})){
		$ist=$i_hosts->{$host}->{"hostxp"}->find('string(/opt/sinks[contains(@name,"'.$i_hosts->{$host}->{"sinkmatch"}.'")]/@volume)');
	}else{
		$ist=$i_hosts->{$host}->{"hostxp"}->find('string(/opt/sinks[@index="0"]/@volume)');
	}
	$ist=eval($ist);
	print "Ist: $ist";
	my $index;
	my $maxvol=maxvol($host);
	if($step=~/^[+-]?\d+$/){
		if(defined($i_hosts->{$host}->{"laut"})){
			foreach my $value(@{$i_hosts->{$host}->{"laut"}}){
				if($ist>$value){$i++;}
			}
			if($step=~/^\+/){
				$i++;
			}elsif($step=~/^-/){
				$i--;
			}else{
				$i=$step;
			}
			if($i+1>@{$i_hosts->{$host}->{"laut"}}){
				$i=@{$i_hosts->{$host}->{"laut"}}-1;
			}
			if($i<0){$i=0;}
			$i=@{$i_hosts->{$host}->{"laut"}}[$i];
		}else{
            if($step=~/^[+-]/){
                $i=$step+$ist;
            }else{
                $i=$step;
            }
            if($i<0){$i=0;}
            if($i>100){$i=100;}
        }
	}else{
		return "";
	}
	if(defined($i_hosts->{$host}->{"sinkmatch"})){
		$index=$i_hosts->{$host}->{"hostxp"}->find('string(/opt/sinks[contains(@name,"'.$i_hosts->{$host}->{"sinkmatch"}.'")]/@index)');
	}else{
		$index=$i_hosts->{$host}->{"hostxp"}->find('string(/opt/sinks[@index="0"]/@index)');
	}
	if($i>$maxvol){$i=$maxvol;}
	my $cmd="/usr/bin/pactl -s $host set-sink-volume $index $i"."% &";
	print $cmd."\n";
	`$cmd`;
	undef($hosts->{$host}->{"clientupdated"});
}


# change the song currently played
sub musik_song{
	#print "musik_song..";
	my $host=$_[0];
	my $step=$_[1];
	my $mnumber=musik_number($host);
	if($mnumber != 0){ $step=$mnumber;}
	if($step==0){
		$step="+1";
	}
	if($step=~/^(\+|\-)(\d+)/){
		my $song=$i_hosts->{$host}->{"mpd"}->current_song();
		my $pos=$song->{"Pos"};
		$pos=$pos+$step;
		$i_hosts->{$host}->{"mpd"}->play($pos);
	}else{
		$i_hosts->{$host}->{"mpd"}->play($step-1);
	}
	manage_offtimer($host,180);
}
=pod
sub musik_mute{
	my $host=$_[0];
#	`pactl -s $host list sinks | grep -q Stumm:.yes && pactl -s $host set-sink-mute 0 0 || pactl -s $host set-sink-mute 0 1`;
}
=cut

# get the total lenght in seconds of the played song
sub musik_getseconds{
	#print "musik_getseconds..";
	my $host=$_[0];
	my $song=$i_hosts->{$host}->{"mpd"}->current_song();
	my $file="/data/medien/music/".$song->{"uri"};
	if($file eq "/data/medien/music/" || $file=~/http/){
		return "1";
	}
	my $info = get_mp3info($file);
	my $length=$info->{"SECS"};
	if($length <1){return "1";}
	return $length;
}

# return the current playing position in seconds
sub musik_getelapsed{
	#print "musik_getelapsed..";
	my $host=$_[0];
	my $status=$i_hosts->{$host}->{"mpd"}->update_status();
	my $pos=$status->{"elapsed"};
	if(!defined($pos)){
		return "0";
	}
	return $pos;
}

# return the ID of the current song. 
sub musik_getid{
	my $host=$_[0];
	my $status=$i_hosts->{$host}->{"mpd"}->update_status();
	my $id=$status->{"songid"};
		if(!defined($id)){
		return "0";
	}
	print "SongID: $id\n";
	return $id;
}

# return the current playing position in a song in percent
sub musik_getpercent{
	#print "musik_getpercent..";
	my $host=$_[0];
	my $pos=musik_getelapsed($host);
	my $length=musik_getseconds($host);
	if( (not looks_like_number($length)) || $length<1){return "0";}
	if(!defined($pos)){
		return "0";
	}
	return sprintf("%2d",$pos/$length*100);
}
=pod
sub musik_getelapsedstring{
	my $host=$_[0];
	my $i_hosts->{$host}->{"mpd"} = Net::MPD->connect("192.168.2.2:".$i_hosts->{"$host"}->{"port"});
	my $song=$i_hosts->{$host}->{"mpd"}->current_song();
	my $status=$i_hosts->{$host}->{"mpd"}->update_status();
	#print Dumper($status);
	#print Dumper($song);
	my $file="/data/medien/music/".$song->{"uri"};
	#print "Port: ".$i_hosts->{$host}->{"mpd"}_channels->{"$host"};
	if($file eq "/data/medien/music/" || $file=~/http/){
		return "";
	}
	my $info = get_mp3info($file);
	my $length=$info->{"TIME"};
	if($length <1){return "";}
	my $pos=$status->{"elapsed"};
	if(!defined($pos)){
		return "";
	}
	my $mm=$pos/60;
	my $ss=$pos%60;
	my $string=sprintf("%3d",$mm).":".sprintf("%2d",$ss)."/".$length;

	return $string;
}

sub musik_limitvol{
	my $host=$_[0];
	my $maxvol = musik_checkmaxvol($host);
	if($maxvol ==0){
		musik_switchoff($host);
		return "switched off";
	}
	my $ist=musik_getvol($host);
	$ist=~s/\%//;
	if($ist eq "") {return;}
	Log 1,"max: $maxvol, ist: $ist";
	if($maxvol<$ist){
		musik_vol($host,$maxvol);
		return "set to $maxvol";
	}
	return "done nothing";
}
=cut
=pod
sub musik_vol{
	my $host=$_[0];
	my $step=$_[1];
        my $i=0;
	if(!(defined($step))){
		$step="+10";
	}
	my $maxvol = musik_checkmaxvol($host);
	my $ist=musik_getvol($host);
	$ist=~s/\%//;
	if($ist eq "") {return;}
	$step=~s/\%//;
	if($step=~/^[+-]?\d+$/){
		if(defined($lautstaerken->{"$host"})){
			foreach my $value(@{$lautstaerken->{"$host"}}){
				if($ist>$value){$i++;}
			}
			if($step=~/^\+/){
				$i++;
			}elsif($step=~/^-/){
				$i--;
			}else{
				$i=$step;
			}
			if($i+1>@{$lautstaerken->{"$host"}}){
				$i=@{$lautstaerken->{"$host"}}-1;
			}
			if($i<0){$i=0;}
			$i=@{$lautstaerken->{"$host"}}[$i];
			
		}else{
                    if($step=~/^[+-]/){
                        $i=$step+$ist;
                    }else{
                        $i=$step;
                    }
                    if($i<0){$i=0;}
                    if($i>100){$i=100;}
                }
	}else{
		return "";
	}
	if($i>$maxvol){$i=$maxvol;}
	$i=$i."%";	
	`pactl -s $host -- set-sink-volume 0 $i`;
	open OUT, ">/data/misc/bin/bginfo_vol$host.txt";
    print OUT $i;
	close OUT;
	return $i;
}
=cut
# do a fast forward or rewind or seek to a specific position in percentage
sub musik_seek{
	#print "musik_seek..";
	my $host=$_[0];
	my $step=10*musik_number($host) || $_[1];
	$step=~s/\%//;
	#my $status=$i_hosts->{$host}->{"mpd"}->update_status();
	my $percent=musik_getpercent($host);
	print "Percent: $percent\n";
	if($percent eq ""){return "";}	
	if($step=~/^[+-]+/){
		$percent=$percent+$step
	}else{
		$percent=$step;
	}
	print "..Percent: $percent\n";
	if($percent>95){$percent=95;}
	if($percent<=0){$percent=0;}
	my $seconds=musik_getseconds($host);
	print "Seconds: $seconds\n";
	$step=$seconds*($percent/100);
	my $elapsed = musik_getelapsed($host);
	if($elapsed<30 && $step >40){
		$step=42;
	}
	my $songid=musik_getid($host);
	$i_hosts->{$host}->{"mpd"}->seek_id($songid,sprintf("%d",$step));
}
=cut
=pod
sub musik_listandere{
	my $host=$_[0];
	my $name;
	my $port;
	my @liste;
	while ( ($name, $port) = each %{$i_hosts->{$host}->{"mpd"}_channels}	 ){
       if($name eq $host){next;}
	   if(ReadingsVal("pa_$name","tuned_channel","0") eq "" || ReadingsVal("pa_$name","tuned_channel","0") ne $i_hosts->{$host}->{"mpd"}_channels->{"$name"}){next;}
	   push(@liste,$name);
    }
	return(@liste);
}
=cut

# change the MPD playlist for a host. 
sub musik_playlist{
	#print "musik_playlist..";
  my $host=$_[0];
  my $step=musik_number($host) ||$_[1];
  my $current_list;
  if( not defined($hosts->{$host}->{"playlist"})){$hosts->{$host}->{"playlist"}=1;}
  $current_list=$hosts->{$host}->{"playlist"};
  my @playlists=$i_hosts->{$host}->{"mpd"}->list_playlists();
  my @listen;
  foreach my $playlist(@playlists){
    if($playlist->{playlist}=~/$host(\d\d\d)/i){
      push @listen,$1;
    }
  }
  @listen= sort(@listen);
  musik_statesave($host,"pl_".sprintf("%02d",$current_list));
  $i_hosts->{$host}->{"mpd"}->clear();
  my $size=@listen;
  
  if($step=~/\-/ || $step=~/\+/){
    $current_list--;
	$current_list=($current_list+$step)%$size;
	$current_list++;
  }else{
	$current_list=$step%$size;
  }
  $hosts->{$host}->{"playlist"}=$current_list;
  my @ansage;
  $i_hosts->{$host}->{"mpd"}->load("$host".$listen[$current_list-1]);
  @ansage=(100+$listen[$current_list-1],);
  $i_hosts->{$host}->{"mpd"}->play(0);
  musik_stateload($host,"pl_".$listen[$current_list-1]);
  ansage($host,\@ansage);
  manage_offtimer($host,180);
}

=pod
sub musik_checkon{
	my $host=$_[0];
	if(musik_checkmaxvol($host) == 0 ) {musik_switchoff($host);return;}
	if($host eq "nele"){
		if($value{'dockstarmusik'} ne "on"){fhem "set dockstarmusik on";}
	}
	if($host eq "merle"){
		if($value{'merlemusik'} ne "on"){fhem "set merlemusik on";}
	}
    my $result=ReadingsVal("pa_$host","tuned_channel","");
	if($result=~/(\d)/	){
		Log 1, "$host war schon an";
	}else{
		musik_switchon($host);
	}
	fhem "delete ".$host."music_offtimer";
	fhem "define ".$host."music_offtimer at +04:00:00 {musik_switchoff(\"$host\");;}";
}
=cut

