#!/usr/bin/perl
# ---------------------------------------------------------------------------- 
# Oracle Trace File Analyzer
# Copyright (C) 2004 Vincent Desjardins (vdesjardins@gmail.com)
# 
# This program is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public License
# as published by the Free Software Foundation; either version 2
# of the License, or (at your option) any later version.
# 
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
# 
# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software
# Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
# ---------------------------------------------------------------------------- 

use strict;
use warnings;
use Data::Dumper;

package OTRCA;

#-----------------------------------------------------------------------------
# Constants
#-----------------------------------------------------------------------------
use constant TIME_RES_9I        => 1000000;
use constant TIME_RES_BEFORE_9I => 100;

#-----------------------------------------------------------------------------
# Variables
#-----------------------------------------------------------------------------
my $gnu_trcres = TIME_RES_9I;

my $gst_header = 'Warning: Not Parsed';
# trace file resolution. Default in centisecond (cs). Was used before 9i releases.
my $gnu_stmtIndex = 1;

# Contain the global resource profile
my $gha_globRespTimeComp = {};
my $g_totalTime = 0;
my $sumElapseWaits = 0;
my $gha_keyMapping = {};
my $gha_tempActions = ();
my $gha_stmts = {};
my $gha_tempwaits = {};
my $gha_recSQLList = {};

# transaction processing
my $gsc_commit = 0;
my $gsc_commitReadOnly = 0;
my $gsc_rollback = 0;
my $gsc_rollbackReadOnly = 0;

# Session Information
my $gsc_sid = 'Warning: Not Parsed';
my $gsc_serial = 'Warning: Not Parsed';

# application info
my $gsc_moduleName = 'Warning: Not Parsed';
my $gsc_moduleHash = 'Warning: Not Parsed';
my $gsc_actionName = 'Warning: Not Parsed';
my $gsc_actionHash = 'Warning: Not Parsed';

# Total Time accounting
my $gsc_trcStartTime = 0;
my $gsc_trcEndTime = 0;    

my $gsc_initialWaitDiscarted = 0;


main(*ARGV);

sub main {
    local(*filehandle) = @_;

    parseTrace(*filehandle);
    #print Data::Dumper::Dumper($gha_stmts);
    printHTMLResult();
}

sub parseTrace {
    local(*filehandle) = @_;

    while(<filehandle>)  {
        my $readedline = $_;

        # 10.2 
        if ($readedline =~ m/^WAIT\s\#(\d+):             # stmt identifier
                             \s+nam=\'(.+)\'             # wait name
                             \s+ela=\s*(\d+)             # elapse time
                             \s+(.+)=(.+)                # p1Text + value
                             \s+(.+)=(.+)                # p2Text + value
                             \s+(.+)=(.+)                # p3Text + value
                             \sobj\#=(.+)
                             \stim=(.+)\s*$              # current time
                            /xo) {
            my $w = { 'id' => $1,
                      'name' => $2,
                      'elapse' => $3,
                      'p1' => $5,
                      'p2' => $7,
                      'p3' => $9,
                      'time' => $11
                    };
            processWaits($w);
            next;
        }

        # 9i + 10.1?
        if ($readedline =~ m/^WAIT\s\#(\d+):             # stmt identifier
                             \s+nam=\'(.+)\'             # wait name
                             \s+ela=\s*(\d+)             # elapse time
                             \s+p1=(.+)                  # p1 value
                             \s+p2=(.+)                  # p2 value
                             \s+p3=(.+)\s*$              # p3 value
                            /xo) {
            my $w = { 'id' => $1,
                      'name' => $2,
                      'elapse' => $3,
                      'p1' => $4,
                      'p2' => $5,
                      'p3' => $6
                    };
            processWaits($w);
            next;
        }
    
        if ($readedline =~ m/^((?:PARSE|EXEC|FETCH|UNMAP|SORT UNMAP))  # action performed
                             \s\#(\d+):                                # stmt identifer
                             c=(\d+),                                  # cpu
                             e=(\d+),                                  # elapse
                             p=(\d+),                                  # physical reads
                             cr=(\d+),                                 # consistent reads
                             cu=(\d+),                                 # current reads
                             mis=(\d+),                                # library cache misses
                             r=(\d+),                                  # rows
                             dep=(\d+),                                # recursive depth of the statement
                             og=(\d+),                                 # optimizer goal
                             tim=(\d+)\s*$                             # current time
                            /xo)  {
            cursorAction($1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11, $12);
            next;
        }
    
        if ($readedline =~ m/^PARSING\sIN\sCURSOR\s\#(\d+)  # stmt identifier
                             \s+len=(\d+)                   # length of the statement
                             \s+dep=(\d+)                   # recursive depth of the statement
                             \s+uid=(\d+)                   # User ID
                             \s+.+tim=(\d+)                 # current time
                             \s+hv=(\d+)                    # handle value
                             \s+ad=\'(\w+)\'\s*$            # stmt address
                            /xo) {
            parseInCursor($1,$2,$3,$4,$5,$6, $7,*filehandle);
            next;
        }
    
        if ($readedline =~ m/^STAT\s\#
                            (\d+)                       # stmt identifier
                            \s+id=(\d+)                 # Stat ID
                            \s+cnt=(\d+)                # Row Count
                            \s+pid=(\d+)                # Parent Stat ID
                            \s+pos=(\d+)                # Indentation
                            \s+obj=(\d+)                # Object ID
                            \s+op=\'(.+)\'              # Operation performed
                           /xo) {
            cursorStat($1, $2, $3, $4, $5, $6, $7);
            next;
        }
     
        if ($readedline =~ m/^XCTEND\s
                             rlbk=(\d+),             # Rollback or commit?
                             rd_only=(\d+)$          # Read-only Transaction?
                            /xo) {
            processTransaction($1, $2);
            next;
        }
    
        if ($readedline =~ m/^\*\*\*\sSESSION\sID:\(
                             (\d+)\.                 # SID
                             (\d+)\)                 # serial#
                             \s+.+$                  # date and time
                            /xo) {
            processSessionInfo($1, $2);
            next;
        }
    
        if ($readedline =~ m/^APPNAME
                             \smod=\'(\S*)\'         # Module Name
                             \smh=(\S+)              # Module Hash value
                             \sact=\'(\S*)\'         # Action Name
                             \sah=(\S+)$             # Action Hash value
                            /xo) {
            processApplicationInfo($1, $2, $3, $4);
            next;
        }
        
        if ($readedline =~ m/^ERROR
                             \s\#(\d+):             # stmt identifier
                             err=(\d+)              # error number
                             \stim=(\d+)            # time
                             /xo) {
            processError($1, $2, $3);
            next;
        }
    }
}

sub processError {
    my ($stmtid, $err, $time) = @_;

    # Retreive the current statement information.
    my $ha_key = $gha_keyMapping->{$stmtid};

    # handle of the current query
    my $handle = $ha_key->{'handle'};
    
    # retreive stmt
    my $ha_stmt = $gha_stmts->{$handle};

    # Add an error
    $ha_stmt->{'errors'}->{'count'} ++;
    $ha_stmt->{'errors'}->{$err} ++;
}

sub processTransaction {
    my ($tStatus, $readonly) = @_;
    
    if ($tStatus > 0)  {
        $gsc_commit ++;
        $gsc_commitReadOnly ++ if ($readonly > 0);
    }
    else {
        $gsc_rollback ++;
        $gsc_rollbackReadOnly ++ if ($readonly > 0);
    }
}

sub processSessionInfo {
    my ($sid, $serial) = @_;
    
    if (defined $gsc_sid && $gsc_sid eq $sid && $gsc_serial eq $serial) {
        print STDERR "Warning: File contains trace information for more than one session.\n";
    }
    else {
        $gsc_sid = $sid;
        $gsc_serial = $serial;
    }
}

sub processApplicationInfo() {
    ($gsc_moduleName, $gsc_moduleHash, $gsc_actionName, $gsc_actionHash) = @_;
}

sub processWaits {
    my($w) = @_;
    
    # Set the timestamp. Used for total elapse time accounting in the trace file
    if ($gsc_trcStartTime == 0) {
        if (defined($w->{'time'}))  {
            $gsc_trcStartTime = $w->{'time'};
        }
        else {
            $gsc_trcEndTime = $w->{'time'};
        }
    }

    if (defined($w->{'time'}) && $gsc_initialWaitDiscarted == 0) {
      $gsc_initialWaitDiscarted = 1;
    } else {
        # build ressource profile
        $gha_globRespTimeComp->{$w->{'name'}}->{'elapse'} += $w->{'elapse'};
        $gha_globRespTimeComp->{$w->{'name'}}->{'nbcalls'} ++;
        $sumElapseWaits += $w->{'elapse'};
        
        # Set the previous depth. Will be used to determine if a wait event is a idle one
        if (exists($gha_keyMapping->{$w->{'id'}}->{'depth'}))
        {
            $w->{'prevDepth'} = $gha_keyMapping->{$w->{'id'}}->{'depth'};
            $w->{'prevHandle'} = $gha_keyMapping->{$w->{'id'}}->{'handle'};
        }
        else {
            $w->{'prevDepth'} = 0;
            $w->{'prevHandle'} = 'invalid';
        }
        
        push(@{$gha_tempwaits->{$w->{'id'}}->{'collection'}}, $w);
    }
}

sub addResourceForProfile {
    my ($eventName, $elapse, $handle, $handlePrev) = @_;
    
    # Build profile for this specific ressource
    my $stmtInfo = $gha_globRespTimeComp->{$eventName}->
        {'stmts'}->{$handle};
    
    $stmtInfo->{'elapse'} += $elapse;
    $stmtInfo->{'nbcalls'} ++;
    $stmtInfo->{'handlePrev'} = $handlePrev if (defined($handlePrev));
    
    $gha_globRespTimeComp->{$eventName}->
        {'stmts'}->{$handle} = $stmtInfo;
}

sub addResourceForStmt {
    my ($eventName, $elapse, $handle, $aggType) = @_;
    
    # Build profile for this specific ressource
    my $stmtInfo = $gha_stmts->{$handle};
    
    my $event = $stmtInfo->{'profile'}->{$aggType}->{'components'}->{$eventName};
    $event->{'elapse'} += $elapse;
    $event->{'nbcalls'} ++;
    $stmtInfo->{'profile'}->{$aggType}->{'components'}->{$eventName} = $event;
}

sub addStmtInfoForStmt {
    my ($handle, $action, $elapse, $cpu, $physicalReads, $consistentReads,
        $currentReads, $cachemisses, $rows, $optimizer, $aggType, $sumWait) = @_;
    
    # Build profile for this specific ressource
    my $stmtInfo = $gha_stmts->{$handle};
    my $actionInfo = $stmtInfo->{$action}->{$aggType};
    
    $actionInfo->{'nbcalls'} ++;
    $actionInfo->{'elapse'} += $elapse;
    $actionInfo->{'CPU'} += $cpu;
    $actionInfo->{'physicalReads'} += $physicalReads;
    $actionInfo->{'consistentReads'} += $consistentReads;
    $actionInfo->{'currentReads'} += $currentReads;
    $actionInfo->{'rows'} += $rows;
    $stmtInfo->{$action}->{$aggType} = $actionInfo;
 
    $stmtInfo->{'cachemisses'} += $cachemisses;
    $stmtInfo->{'optimizer'} = $optimizer;

    my $profileInfo = $stmtInfo->{'profile'}->{$aggType};
    $profileInfo->{'waittime'} += $sumWait;
    $profileInfo->{'elapse'} += $elapse;
    $profileInfo->{'CPU'} += $cpu;
    $profileInfo->{'nbcalls'} ++;
    $stmtInfo->{'profile'}->{$aggType} = $profileInfo;

    $gha_stmts->{$handle} = $stmtInfo;
}

sub setStmtToZero {
    my $stmtInfo;
    
    $stmtInfo->{'nbcalls'} = 0;
    $stmtInfo->{'elapse'} = 0;
    $stmtInfo->{'CPU'} = 0;
    $stmtInfo->{'physicalReads'} = 0;
    $stmtInfo->{'consistentReads'} = 0;
    $stmtInfo->{'currentReads'} = 0;
    $stmtInfo->{'rows'} = 0;
    
    return $stmtInfo;
}

sub cursorAction {
    my($action, $stmtid, $cpu, $elapse, $physicalReads, $consistentReads, 
        $currentReads, $cachemisses, $rows, $depth, $optimizer, $time) = @_;
    
    # Set the timestamp. Used for total elapse time accounting in the trace file
    if ($gsc_trcStartTime == 0)  {
        $gsc_trcStartTime = $time;
        $gsc_initialWaitDiscarted = 1;
    }
    else {
        $gsc_trcEndTime = $time;
    }

    # Verify that the statement exists
    if (!exists($gha_keyMapping->{$stmtid})) {
        print STDERR "Cursor # $stmtid for Action $action is not defined.\n";
        print STDERR "    Cause: Cursor probably defined in another trace file.\n";
        return;
    }

    # Retreive the current statement information.
    my $ha_key = $gha_keyMapping->{$stmtid};

    # handle of the current query
    my $handle = $ha_key->{'handle'};
    
    # build ressource profile
    if ($depth == 0) {
        #$gha_globRespTimeComp->{'CPU'}->{'elapse'} += $cpu;
        $g_totalTime += $elapse;
    }
    
    # now apply wait to the action
    my $sumWait = processWaitOnAction($handle, $stmtid, $depth, $elapse);
    
    # Add action information to the statement (including recursive SQL).
    addStmtInfoForStmt($handle, $action, $elapse, $cpu, $physicalReads, 
        $consistentReads, $currentReads, $cachemisses, $rows, $optimizer, 
        'agg', $sumWait);
    
    # Processing of ressource aggregation in recursive SQL.
    processCPUComponent($handle, $action, $elapse, $cpu, $physicalReads, 
        $consistentReads, $currentReads, $cachemisses, $rows, $depth, 
        $optimizer, $sumWait);

    # Build a list of child SQL
    processRecursiveSQLList($handle,$depth);
}

sub processRecursiveSQLList {
    my ($handle, $depth) = @_;

    my $ha_stmtInfo = $gha_stmts->{$handle};
    my $ha_recSQLs = $gha_recSQLList->{$depth+1};

    map { 
        $ha_stmtInfo->{'recSQLList'}->{$_}->{'count'} += $ha_recSQLs->{$_}->{'count'};
        $gha_stmts->{$_}->{'parent'} = $handle;
    } keys %{$ha_recSQLs};

    delete $gha_recSQLList->{$depth+1};
    $gha_recSQLList->{$depth}->{$handle}->{'count'} ++;
}

sub processWaitOnAction() {
    my ($handle, $stmtid, $depth, $elapse) = @_;
    
    # Remove and process all idle wait events from all collections
    my $waitList = $gha_tempwaits->{$stmtid}->{'collection'};
    my $sumWait = 0;
    
    foreach my $event (@{$waitList}) {
        my $tmphandle;
        my $tmphandlePrev;
        $tmphandle = $handle;
        
        # check if this is a idle wait event
        if ($event->{'elapse'} > $elapse && $event->{'prevDepth'} == 0) {
            $g_totalTime += $event->{'elapse'};
            
            $tmphandle = "$tmphandle";
            if ($event->{'prevHandle'} ne $tmphandle) {
                $tmphandlePrev = "$event->{'prevHandle'}";
            }
        }
        else {
            # add this wait to the total time. Will be used to determine
            # if we have some unaccounted-for time in statement
            $sumWait += $event->{'elapse'};
        
            addResourceForStmt($event->{'name'}, $event->{'elapse'}, $tmphandle, 'noagg');
        }
        
        # Add statement to the correspinding statement resource profile
        addResourceForProfile($event->{'name'}, $event->{'elapse'}, $tmphandle, $tmphandlePrev);
        
        # Clear the prevDepth because we do not need it anymore
        delete $event->{'prevDepth'};
        delete $event->{'prevHandle'};
     }

    # Clear the temporary wait list for the next action.
    delete ($gha_tempwaits->{$stmtid});
    
    return $sumWait;
}

sub processCPUComponent() {
    my($handle, $action, $elapse, $cpu, $physicalReads, $consistentReads, 
        $currentReads, $cachemisses, $rows, $depth, $optimizer, $sumWait) = @_;
   
    # depth = 0 elements are not pushed on the stack.
    my $prevActionInfo = pop(@{$gha_tempActions});
    if (defined($prevActionInfo)) {
        if ($depth > $prevActionInfo->{'depth'}) {
            push(@{$gha_tempActions}, $prevActionInfo);
            my $actionInfo = {};
            actionComponentDefault($actionInfo, $handle, $action, $elapse, $cpu, $physicalReads, 
                $consistentReads, $currentReads, $cachemisses, $rows, $depth, $optimizer, $sumWait);
        }
        elsif ($depth == $prevActionInfo->{'depth'}) {
            my $actionInfo = $prevActionInfo;
            
            actionComponentDefault($actionInfo, $handle, $action, $elapse, $cpu, $physicalReads, 
                $consistentReads, $currentReads, $cachemisses, $rows, $depth, $optimizer, $sumWait);
        }
        else { # $depth < $prevActionInfo->{'depth'} {
            actionComponentParent($prevActionInfo, $handle, $action, $elapse, $cpu, $physicalReads, 
                $consistentReads, $currentReads, $cachemisses, $rows, $depth, $optimizer, $sumWait);
        }
    }
    elsif ($depth > 0) {
        my $actionInfo = {};
        actionComponentDefault($actionInfo, $handle, $action, $elapse, $cpu, $physicalReads, $consistentReads,
            $currentReads, $cachemisses, $rows, $depth, $optimizer, $sumWait);
    }
    else { # $depth == 0 {
        processResource($cpu, $cpu, $elapse, $elapse, $handle, $action, 
            $physicalReads, $consistentReads, $currentReads, 
            $cachemisses, $rows, $optimizer, $sumWait);
    }
}

sub actionComponentDefault {
    my ($actionInfo, $handle, $action, $elapse, $cpu, $physicalReads, $consistentReads,
        $currentReads, $cachemisses, $rows, $depth, $optimizer, $sumWait) = @_;
    
    createActionHistoryEntry($actionInfo, $handle, $depth, $cpu, $elapse, $physicalReads, 
        $consistentReads, $currentReads);
    push(@{$gha_tempActions}, $actionInfo);
            
    processResource($cpu, $cpu, $elapse, $elapse, $handle, $action, 
        $physicalReads, $consistentReads, $currentReads, 
        $cachemisses, $rows, $optimizer, $sumWait);
}

sub actionComponentParent {
    my ($prevActionInfo, $handle, $action, $elapse, $cpu, $physicalReads, $consistentReads,
        $currentReads, $cachemisses, $rows, $depth, $optimizer, $sumWait) = @_;

    my $usedCPU = $cpu - $prevActionInfo->{'CPU'};
    my $usedElapse = $elapse - $prevActionInfo->{'elapse'};
    my $usedPhysicalReads = $physicalReads - $prevActionInfo->{'PhysicalReads'};
    my $usedConsistentReads = $consistentReads - $prevActionInfo->{'ConsistentReads'};
    my $usedCurrentReads = $currentReads - $prevActionInfo->{'CurrentReads'};
    $usedCPU = 0 if ($usedCPU < 0);
    $usedElapse = 0 if ($usedElapse < 0);
    $usedPhysicalReads = 0 if ($usedPhysicalReads < 0);
    $usedConsistentReads = 0 if ($usedConsistentReads < 0);
    $usedCurrentReads = 0 if ($usedCurrentReads < 0);
    
    processResource($cpu, $usedCPU, $elapse, $usedElapse, $handle, $action, 
        $usedPhysicalReads, $usedConsistentReads, $usedCurrentReads, 
        $cachemisses, $rows, $optimizer, $sumWait);
    
    if ($depth > 0) {
        my $prevPrevActionInfo = pop(@{$gha_tempActions});
        if (defined($prevPrevActionInfo)) {
            if ($depth == $prevPrevActionInfo->{'depth'}) {
                createActionHistoryEntry($prevPrevActionInfo, $handle, $depth, $cpu, $elapse, $physicalReads, 
                    $consistentReads, $currentReads);
            }
            push(@{$gha_tempActions}, $prevPrevActionInfo);
        }
    }
 }

sub createActionHistoryEntry {
    my ($actionInfo, $handle, $depth, $cpu, $elapse, $physicalReads, $consistentReads, $currentReads) = @_;
    
    $actionInfo->{'depth'} = $depth;
    $actionInfo->{'CPU'} += $cpu;
    $actionInfo->{'elapse'} += $elapse;
    $actionInfo->{'PhysicalReads'} += $physicalReads;
    $actionInfo->{'ConsistentReads'} += $consistentReads;
    $actionInfo->{'CurrentReads'} += $currentReads;
    $actionInfo->{'handle'} = $handle;
}

sub processResource {
        my($cpu, $usedCPU, $elapse, $usedElapse, $handle, $action,
           $physicalReads, $consistentReads, $currentReads, 
           $cachemisses, $rows, $optimizer, $sumWait) = @_;

    processCPUResource($cpu, $usedCPU, $handle);
    processUnacountedForResource($cpu, $usedCPU, $sumWait, $elapse, $usedElapse, $handle);
    addStmtInfoForStmt($handle, $action, $usedElapse, $usedCPU, $physicalReads,
        $consistentReads, $currentReads, $cachemisses, $rows, $optimizer,
        'noagg', $sumWait);
}

sub processCPUResource {
    my ($cpu, $usedCPU, $handle) = @_;

    if ($usedCPU > 0) {
        $gha_globRespTimeComp->{'CPU'}->{'nbcalls'} ++;
        $gha_globRespTimeComp->{'CPU'}->{'elapse'} += $usedCPU;
        addResourceForProfile('CPU', $usedCPU, $handle);
        addResourceForStmt('CPU', $usedCPU, $handle, 'noagg');
        addResourceForStmt('CPU', $cpu, $handle, 'agg');
    }
}

sub processUnacountedForResource {
    my ($cpu, $usedCPU, $sumWait, $elapse, $usedElapse, $handle) = @_;
    
    my $unacFor = $elapse - $cpu - $sumWait;
    my $usedUnacFor = $usedElapse - $usedCPU - $sumWait;

    if ($usedUnacFor > 0) {
        $gha_globRespTimeComp->{'unacounted-for'}->{'nbcalls'} ++;
        $gha_globRespTimeComp->{'unacounted-for'}->{'elapse'} += $usedUnacFor;
        addResourceForProfile('unacounted-for', $usedUnacFor, $handle);
        addResourceForStmt('unacounted-for', $usedUnacFor, $handle, 'noagg');
        addResourceForStmt('unacounted-for', $unacFor, $handle, 'agg');
    }
}  

sub cursorStat {
    my ($stmtid, $statid, $count, $pid, $pos, $obj, $op) = @_;
    
    my $ha_key = $gha_keyMapping->{$stmtid};
    my $handle = $ha_key->{'handle'};
    my $stmtInfo = $gha_stmts->{$handle};
    
    if (!exists($stmtInfo->{'stats'}->{$statid})) {
        my $statInfo;
        $statInfo->{'statid'} = $statid;
        $statInfo->{'count'} = $count;
        $statInfo->{'pid'} = $pid;
        $statInfo->{'pos'} = $pos;
        $statInfo->{'obj'} = $obj;
        $statInfo->{'op'} = $op;
    
        $stmtInfo->{'stats'}->{$statid} = $statInfo;
    }
}

sub parseInCursor {
    my ($stmtid, $length, $depth, $userID, $time, $handle, $address, $filehandle) = @_;
    
    my $ha_stmtInfo;
    $ha_stmtInfo->{'stmtid'} = $stmtid;
    $ha_stmtInfo->{'length'} = $length;
    $ha_stmtInfo->{'depth'} = $depth;
    $ha_stmtInfo->{'userid'} = $userID;
    $ha_stmtInfo->{'time'} = $time;
    $ha_stmtInfo->{'handle'} = $handle;
    $ha_stmtInfo->{'address'} = $address;
    $ha_stmtInfo->{'index'} = $gnu_stmtIndex;
    $gnu_stmtIndex ++;
    
    my $sc_readedline = <$filehandle>;
    my $sc_sqlstring = "";
    while($sc_readedline !~ m/^END OF STMT/) {
        $sc_sqlstring .= $sc_readedline;
        $sc_readedline = <$filehandle>;
    }
    
    $ha_stmtInfo->{'text'} = $sc_sqlstring;
    
    $gha_stmts->{$handle} = $ha_stmtInfo 
        unless (defined($gha_stmts->{$handle}));
    my $ha_key;
    $ha_key->{'depth'} = $depth;
    $ha_key->{'handle'} = $handle;
    $gha_keyMapping->{$stmtid} = $ha_key;
    
    # Process population of the recursive SQL list
    $gha_recSQLList->{$handle}->{'count'} ++;
}

sub processHeader {
    local(*filehandle) = @_;

    my $lineNumber = 1;
    my $line = <filehandle>;
    
    while ($line !~ m/^\s+$/ && $lineNumber < 5) {
        if ($line !~ m/^\s+$/) {
            if ($line !~ m/^\*\*\*.+$/) {
                $gst_header .= $line;
            }
    
            # check the Oracle Version to set the precision denominator.
            if ($line =~ m/^Oracle(\d+)/) {
                # 9i and greater the resolution is in microsecond (us).
                # 8i and lower the resolution is in centisecond (cs).
                if ($1 < 9) {
                    $gnu_trcres = TIME_RES_BEFORE_9I;
                }
            }
        }
        
        $lineNumber ++;
        $line = <filehandle>;
    }
}

sub formatSQL {
    #arguments
    my ($sqlStr) = @_;
    #constants
    my $indentSize = 7;
    my $tokenSize = 6;
    my $maxLineSize = 80;
    #variables
    my @array = split(/(\s+|\(|\)|\,)/, $sqlStr);
    my $prevItem = "";
    my $pLevel = 1;
    my $prevLevel;
    my $lLength = 0;
    my $curLine = 1;
    
    $prevLevel->{0}->{'curLine'} = $curLine;
    $prevLevel->{0}->{'lLength'} = $lLength;
    $prevLevel->{0}->{'indent'} = 0;
    
    foreach my $item (@array) {
        if ($item !~ m/^\s*$/) {
            if (uc($item) eq 'SELECT' ||
                uc($item) eq 'UPDATE' ||
                uc($item) eq 'DELETE' ||
                uc($item) eq 'INSERT' ||
                uc($item) eq 'FROM' ||
                uc($item) eq 'WHERE' ||
                uc($item) eq 'AND' ||
                uc($item) eq 'OR' ||
                uc($item) eq 'ORDER' ||
                uc($item) eq 'UNION' ||
                uc($item) eq 'MINUS' ||
                uc($item) eq 'INTERSECT' ||
                uc($item) eq 'GROUP') {
                #my $str = " "x(($pLevel*$indentSize)-length($item)+6) . "$item";
                $prevLevel->{$pLevel-1}->{'indent'} = $indentSize;
                my $str = " "x($prevLevel->{$pLevel-1}->{'lLength'}-length($item)+6) . "$item";
                $lLength = length($str);
                print "\n$str";
                $curLine++;
            }
            else {
                if ($item !~ m/(\(|\)|\,)/) {
                    if ($prevItem =~ m/^(\w+)|(\w+(\.|\w*))$/) {
                        print " ";
                        $lLength++;
                    }
                }
                elsif ($item =~ m/^\w+$/) {
                    if ($prevItem =~ m/^(\w+)|(\w+(\.|\w*))$/) {
                        print " ";
                        $lLength++;
                    }
                }
                if($prevItem =~ m/(\)|\,)/) {
                    if ($item =~ m/^(\w+)|(\w+(\.|\w*))$/) {
                        print " ";
                        $lLength++;
                    }
                    else {
                        #print " ";
                    }
                }
                if($item =~ m/\(/) {
                    $prevLevel->{$pLevel}->{'curLine'} = $curLine;
                    $prevLevel->{$pLevel}->{'lLength'} = $lLength;
                    $prevLevel->{$pLevel}->{'indent'} = 0;
                    $pLevel++;
                }
                if($item =~ m/\)/) {
                    $pLevel--;
                    if ($curLine != $prevLevel->{$pLevel}->{'curLine'}) {
                        my $str = " "x$prevLevel->{$pLevel}->{'lLength'};
                        print "\n" . $str;
                        $lLength = length($str);
                        $curLine++;
                    }
                }
                $lLength += length($item);
                print "$item";

                if($item =~ m/(\,)/ && $lLength > $maxLineSize) {
                    #my $str = " "x(($pLevel*$indentSize)+$indentSize-1);
                    my $str = " "x($prevLevel->{$pLevel-1}->{'lLength'}+
                        $prevLevel->{$pLevel-1}->{'indent'});
                    print "\n" . $str;
                    $lLength = length($str);
                    $curLine++;
                }
            }
            $prevItem = $item;
        }
        else {
            print " ";
        }
    }
    print "\n";
}

sub printHTMLResourceTableHeader {
    my $line1 = "-"x36;
    my $line2 = "-"x17;
    my $line3 = "-"x9;
    my $line4 = "-"x14;
    print <<"EOF";
          <table border=0 cellspacing=0 width=640>
          <tr><td align=left width=330>Response Time Component</td>
          <td align=right width=150>Duration</td>
          <td align=right width=85># Calls</td>
          <td align=right width=115>Duration/Call</td>
          </tr>
          <tr><td align=left width=330>$line1</td>
          <td align=right width=150>$line2</td>
          <td align=right width=85>$line3</td>
          <td align=right width=115>$line4</td>
          </tr>
EOF
}

sub printHTMLResourceTableLine {
    my ($name, $elapse, $nbCalls, $totalTime, $handlePrev) = @_;
   
    print "<tr><td align=left width=330>\n";
    if (defined($handlePrev)) {
        print "<a href=\"#$handlePrev\">$handlePrev</a> - ";
    }
    print "<a href=\"#$name\">$name</a></td>\n";

    printf <<"EOF", $elapse/$gnu_trcres, $elapse/$totalTime*100, $nbCalls, $elapse/$gnu_trcres/$nbCalls;
           <td align=right width=150><table border=0 cellspacing=0 width=150>
           <tr><td align=right width=80>%9.3fs</td>
           <td align=right width=70>%5.1f%%</td></tr></table></td>
           <td align=right width=85>%10.0f</td>
           <td align=right width=115>%13.06fs</td>
           </tr>
EOF
}

sub printHTMLResourceTableFooter {
    my ($elapse) = @_;

    my $line1 = "-"x36;
    my $line2 = "-"x17;
    my $line3 = "-"x9;
    my $line4 = "-"x14;
    
    print <<"EOF";
          <tr><td align=left width=330>$line1</td>
          <td align=right width=150>$line2</td>
          <td align=right width=85>$line3</td>
          <td align=right width=115>$line4</td>
          </tr>
          <tr><td align=left width=330>Total response time</td>
EOF
    printf <<"EOF", $elapse/$gnu_trcres, 100;
           <td align=right width=150><table border=0 cellspacing=0 width=150>
           <tr><td align=right width=80>%9.3fs</td>
           <td align=right width=70>%5.1f%%</td></tr></table></td>
           <td align=right width=85></td>
           <td align=right width=115></td>
           </tr>
           </table>
EOF
}

sub printStmtResult {
    my ($stmtInfoParse, $stmtInfoExec, $stmtInfoUnmap, $stmtInfoSortUnmap, 
        $stmtInfoFetch) = @_;
    
    $stmtInfoParse = setStmtToZero() if (!defined($stmtInfoParse));
    $stmtInfoExec = setStmtToZero() if (!defined($stmtInfoExec));
    $stmtInfoUnmap = setStmtToZero() if (!defined($stmtInfoUnmap));
    $stmtInfoSortUnmap = setStmtToZero() if (!defined($stmtInfoSortUnmap));
    $stmtInfoFetch = setStmtToZero() if (!defined($stmtInfoFetch));
    
    printf "%-10s %8s %12s %12s %11s %11s %11s %11s\n", 
        'Call', 'Count', 'CPU', 'Elapse', 'Disk', 'Query', 'Current', 'Rows';

    printf "%-93s\n", "-"x93;
        
    printf "Parse      %8u %11.3fs %11.3fs %11u %11u %11u %11u\n", 
        $stmtInfoParse->{'nbcalls'}, $stmtInfoParse->{'CPU'}/$gnu_trcres,
        $stmtInfoParse->{'elapse'}/$gnu_trcres, $stmtInfoParse->{'physicalReads'},
        $stmtInfoParse->{'consistentReads'}, $stmtInfoParse->{'currentReads'},
        $stmtInfoParse->{'rows'};
    
    printf "Execute    %8u %11.3fs %11.3fs %11u %11u %11u %11u\n", 
        $stmtInfoExec->{'nbcalls'}, $stmtInfoExec->{'CPU'}/$gnu_trcres,
        $stmtInfoExec->{'elapse'}/$gnu_trcres, $stmtInfoExec->{'physicalReads'},
        $stmtInfoExec->{'consistentReads'}, $stmtInfoExec->{'currentReads'},
        $stmtInfoExec->{'rows'};
        
    printf "Unmap      %8u %11.3fs %11.3fs %11u %11u %11u %11u\n", 
        $stmtInfoUnmap->{'nbcalls'}, $stmtInfoUnmap->{'CPU'}/$gnu_trcres,
        $stmtInfoUnmap->{'elapse'}/$gnu_trcres, $stmtInfoUnmap->{'physicalReads'},
        $stmtInfoUnmap->{'consistentReads'}, $stmtInfoUnmap->{'currentReads'},
        $stmtInfoUnmap->{'rows'};
        
    printf "Sort Unmap %8u %11.3fs %11.3fs %11u %11u %11u %11u\n", 
        $stmtInfoSortUnmap->{'nbcalls'}, $stmtInfoSortUnmap->{'CPU'}/$gnu_trcres,
        $stmtInfoSortUnmap->{'elapse'}/$gnu_trcres, $stmtInfoSortUnmap->{'physicalReads'},
        $stmtInfoSortUnmap->{'consistentReads'}, $stmtInfoSortUnmap->{'currentReads'},
        $stmtInfoSortUnmap->{'rows'};

    printf "Fetch      %8u %11.3fs %11.3fs %11u %11u %11u %11u\n", 
        $stmtInfoFetch->{'nbcalls'}, $stmtInfoFetch->{'CPU'}/$gnu_trcres, 
        $stmtInfoFetch->{'elapse'}/$gnu_trcres, $stmtInfoFetch->{'physicalReads'},
        $stmtInfoFetch->{'consistentReads'}, $stmtInfoFetch->{'currentReads'},
        $stmtInfoFetch->{'rows'};
        
    printf "%-93s\n", "-"x93;
    
    printf "Total      %8u %11.3fs %11.3fs %11u %11u %11u %11u\n", 
        $stmtInfoParse->{'nbcalls'} + $stmtInfoExec->{'nbcalls'}  + 
            $stmtInfoUnmap->{'nbcalls'} + $stmtInfoSortUnmap->{'nbcalls'} + 
            $stmtInfoFetch->{'nbcalls'},
        ($stmtInfoParse->{'CPU'} + $stmtInfoExec->{'CPU'} + 
            $stmtInfoUnmap->{'CPU'} + $stmtInfoSortUnmap->{'CPU'} + 
            $stmtInfoFetch->{'CPU'})/$gnu_trcres,
        ($stmtInfoParse->{'elapse'} + $stmtInfoExec->{'elapse'} + 
            $stmtInfoUnmap->{'elapse'} + $stmtInfoSortUnmap->{'elapse'} + 
            $stmtInfoFetch->{'elapse'})/$gnu_trcres,
        $stmtInfoParse->{'physicalReads'} + $stmtInfoExec->{'physicalReads'} + 
            $stmtInfoUnmap->{'physicalReads'} + 
            $stmtInfoSortUnmap->{'physicalReads'} + 
            $stmtInfoFetch->{'physicalReads'},
        $stmtInfoParse->{'consistentReads'} + 
            $stmtInfoExec->{'consistentReads'} + 
            $stmtInfoUnmap->{'consistentReads'} + 
            $stmtInfoSortUnmap->{'consistentReads'} + 
            $stmtInfoFetch->{'consistentReads'},
        $stmtInfoParse->{'currentReads'} + $stmtInfoExec->{'currentReads'} + 
            $stmtInfoUnmap->{'currentReads'} + 
            $stmtInfoSortUnmap->{'currentReads'} + 
            $stmtInfoFetch->{'currentReads'},
        $stmtInfoParse->{'rows'} + $stmtInfoExec->{'rows'} + 
            $stmtInfoUnmap->{'rows'} + $stmtInfoSortUnmap->{'rows'} + 
            $stmtInfoFetch->{'rows'};
}

sub printHTMLResult {
    print <<EOF;
        <html><head><title>Trace File</title>
        <style type="text/css">
        body { margin-left: 2%; }
        h1  { font-family:Arial,Helvetica,Geneva,sans-serif;font-size:16pt;  }
        h2  { 
            font-family:Arial,Helvetica,Geneva,sans-serif;
            font-size:12pt; 
            margin-left: -1%; 
            margin-top: 1em; 
            margin-bottom: -1em; 
            }
        h3  { 
            font-family:Arial,Helvetica,Geneva,sans-serif;
            font-size:10pt;
            margin-left: -1%; 
            margin-top: 1em; 
            margin-bottom: -1em; 
            }
        pre { font-family:Courier;font-size:10pt }
        table {font-family:Courier;font-size:10pt }
        </style></head><body><pre>
EOF
    
    # Print Header
    print "$gst_header\n\n";
    print "Session SID     : $gsc_sid\n";
    print "Session Serial# : $gsc_serial\n";
    print "Module Name     : $gsc_moduleName\n";
    print "Module Hash     : $gsc_moduleHash\n";
    print "Action Name     : $gsc_actionName\n";
    print "Action Hash     : $gsc_actionHash\n\n";
    
    # Print Total Time Accounting
    my $totalElapse = ($gsc_trcEndTime - $gsc_trcStartTime)/$gnu_trcres;
    printf "Total Elapsed Time of Trace File: %9.3fs\n\n", $totalElapse;
    
    print "<h2>Resource Profile</h2>\n";
    printHTMLResourceTableHeader();
    
    my @items = sort { $gha_globRespTimeComp->{$b}->{'elapse'} <=> 
                       $gha_globRespTimeComp->{$a}->{'elapse'} 
                     } (keys %{$gha_globRespTimeComp});
    for my $item (@items) {
        if ($item eq "unaccounted-for") {
            printf "<tr><td align=left width=330>" . "<a href=\"#$item\">$item</a>" . "</td>" .
                   "<td align=right width=150><table border=0 cellspacing=0 " . 
                   "width=150><tr><td align=right width=80>%9.3fs</td>" . "
                   <td align=right width=70>%5.1f%%</td></tr></table></td>" .
                   "<td align=right width=85></td>" .
                   "<td align=right width=115></td>" .
                   "</tr>", $gha_globRespTimeComp->{$item}->{'elapse'}/$gnu_trcres, 
                $gha_globRespTimeComp->{$item}->{'elapse'}/$g_totalTime*100;
        }
        else {
            printHTMLResourceTableLine($item, $gha_globRespTimeComp->{$item}->{'elapse'},
                $gha_globRespTimeComp->{$item}->{'nbcalls'}, $g_totalTime);
        }
    }

    printHTMLResourceTableFooter($g_totalTime);
    
    # Print wait events
    @items = sort { $gha_globRespTimeComp->{$b}->{'elapse'} <=> 
                    $gha_globRespTimeComp->{$a}->{'elapse'} 
                  } (keys %{$gha_globRespTimeComp});
    for my $item (@items) {
        my $stmts = $gha_globRespTimeComp->{$item}->{'stmts'};
        my @handles = sort { $stmts->{$b}->{'elapse'} <=> 
                             $stmts->{$a}->{'elapse'} 
                           } keys %{$stmts};
        
        print "<br><h3><a name=\"$item\">$item</a></h3>\n";

        printHTMLResourceTableHeader();
        for my $handle (@handles) {
            printHTMLResourceTableLine($handle, $stmts->{$handle}->{'elapse'},
                $stmts->{$handle}->{'nbcalls'}, $gha_globRespTimeComp->{$item}->{'elapse'},
                $stmts->{$handle}->{'handlePrev'});
        }
        printHTMLResourceTableFooter($gha_globRespTimeComp->{$item}->{'elapse'});
    }
    
    print "<br><h3>Statement Lists</h3>\n";
    # print statements
    @items = sort { $gha_stmts->{$a}->{'index'} <=> $gha_stmts->{$b}->{'index'} } (keys %{$gha_stmts});
    for my $item (@items) {
        printf "%-80s\n", "*"x80;
        
        print "<b>Statement Handle     : <a name=\"$item\">$item</a></b>\n";
        print "Parent Statement Handle : <a href=\"#$gha_stmts->{$item}->{parent}\">$gha_stmts->{$item}->{parent}</a>\n" 
            if (exists($gha_stmts->{$item}->{parent}));
        print "Statement Address       : $gha_stmts->{$item}->{address}\n";
        print "Optimizer Goal          : $gha_stmts->{$item}->{optimizer}\n";
        print "Cache Misses            : $gha_stmts->{$item}->{cachemisses}\n";
        print "Recursive Depth         : $gha_stmts->{$item}->{depth}\n";
        print "Parsing User ID         : $gha_stmts->{$item}->{userid}\n";
        print "Errors                  : $gha_stmts->{$item}->{errors}->{count}\n"
            if (exists($gha_stmts->{$item}->{errors}));

        my $stmtInfoParse;
        my $stmtInfoExec;
        my $stmtInfoUnmap;
        my $stmtInfoSortUnmap;
        my $stmtInfoFetch;

        # Print Recursive SQL list
        if (exists($gha_stmts->{$item}->{'recSQLList'})) {
            my $recSQLList = $gha_stmts->{$item}->{'recSQLList'};
            print "\n<b>Recursive SQL Statements Called:</b>\n";
            print "<table><tr><td align=left width=700>";
            map { print "<a href=\"#$_\">($recSQLList->{$_}->{count})$_</a> " } keys %{$recSQLList};
            print "</td></tr></table>";
            
            # Print Result with recursive SQL
            print "\n\n<b>Resources Used By This SQL (With Recursive SQL)</b>\n";
            $stmtInfoParse = $gha_stmts->{$item}->{'PARSE'}->{'agg'};
            $stmtInfoExec = $gha_stmts->{$item}->{'EXEC'}->{'agg'};
            $stmtInfoUnmap = $gha_stmts->{$item}->{'UNMAP'}->{'agg'};
            $stmtInfoSortUnmap = $gha_stmts->{$item}->{'SORT UNMAP'}->{'agg'};
            $stmtInfoFetch = $gha_stmts->{$item}->{'FETCH'}->{'agg'};
            printStmtResult($stmtInfoParse, $stmtInfoExec, $stmtInfoUnmap, 
                $stmtInfoSortUnmap, $stmtInfoFetch);
        }

        # Print Result without recursive SQL
        print "\n<b>Resources Used By This SQL:</b>\n";
        $stmtInfoParse = $gha_stmts->{$item}->{'PARSE'}->{'noagg'};
        $stmtInfoExec = $gha_stmts->{$item}->{'EXEC'}->{'noagg'};
        $stmtInfoUnmap = $gha_stmts->{$item}->{'UNMAP'}->{'noagg'};
        $stmtInfoSortUnmap = $gha_stmts->{$item}->{'SORT UNMAP'}->{'noagg'};
        $stmtInfoFetch = $gha_stmts->{$item}->{'FETCH'}->{'noagg'};
        printStmtResult($stmtInfoParse, $stmtInfoExec, $stmtInfoUnmap, 
            $stmtInfoSortUnmap, $stmtInfoFetch);

        # print resource profile for this query
        print "\nElapsed times include waiting on following events:\n";
        printHTMLResourceTableHeader();

        my $profile = $gha_stmts->{$item}->{'profile'}->{'noagg'};

        my $components = $profile->{'components'};
        
        my @waitnames = sort { $components->{$b}->{'elapse'} <=> 
                               $components->{$a}->{'elapse'} 
                             } (keys %{$components});
        for my $waitname (@waitnames) {
            printHTMLResourceTableLine($waitname, $components->{$waitname}->{'elapse'},
                $components->{$waitname}->{'nbcalls'}, $profile->{'elapse'});
        }
        printHTMLResourceTableFooter($profile->{'elapse'});
        
        # print SQL Text
        print "<b>SQL Text:</b>\n";
        formatSQL($gha_stmts->{$item}->{text});
        print "\n\n";
        
        # print explain plan
        if (exists($gha_stmts->{$item}->{'stats'})) {
            print "<b>Execution Plan:</b>\n";
            print "Rows     Row Source Operation\n";
            print "-------- ---------------------------------------------------\n";
            my $ha_level;
            $ha_level->{0} = 0;
            my $stats = $gha_stmts->{$item}->{'stats'};
            my @orderedstats = sort { $stats->{$a}->{'statid'} <=> 
                                      $stats->{$b}->{'statid'} 
                                    } keys(%{$stats});
            for my $statid (@orderedstats) {
                my $plevel = $ha_level->{$stats->{$statid}->{'pid'}};
                printf "%8u %-s $stats->{$statid}->{op}\n", 
                    $stats->{$statid}->{'count'}, " "x$plevel;
                $ha_level->{$statid} = $plevel+1;
            }
            print "\n";
        }
    }
    print "</pre></body></html>";
}

