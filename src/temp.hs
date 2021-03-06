
This section gives all basic definitions that will be used in all three \Circus\ models. And gateway related definitions are only used in the ESEL System 2.

First of all, three constants are defined. $MAX\_ESEL$ and $MAX\_PID$ stand for maximum number of displays and maximum number of product categories (or, products for short) in the system separately. And constant $MAX\_GATEWAY$ stands for maximum number of gateways.
\begin{zed}
    MAX\_ESEL == \nat \\
\also    MAX\_PID == \nat
%    MAX\_GATEWAY: \nat
\end{zed}

Then all displays and products are identified by a tag plus a unique number which are defined in the free types $ESID$ and $PID$ below where the constructors $ES$ and $PD$ are the tags for displays and products. For an instance, number ten of the display is given $ES~10$ or $ES(10)$. Similarly, $GID$ gives all identities for gateways.
\begin{zed}
    ESID ::= ES \ldata 1 \upto MAX\_ESEL \rdata \\
    PID ::= PD \ldata 1 \upto MAX\_PID \rdata \\
%    GID ::= GW \ldata 1 \upto MAX\_GATEWAY \rdata
\end{zed}

%The map from ESELs to gateways, $gwmap$, is defined as a total function. One ESEL is linked to up to one gateway. However, one gateway may associate with multiple ESELs.
%\begin{axdef}
%    % total function and each ESEL must be assigned to corresponding gateway
%    gwmap: ESID \fun GID
%    \where
%    gwmap = \{(ES~1, GW~1), (ES~2, GW~1), (ES~3, GW~2)\}
%\end{axdef}

The type of product price is defined as an abbreviation to natural numbers $\nat$.
\begin{zed}
    Price == \nat
\end{zed}

The unit response is defined as a free type with two constants: $uok$ and $ufail$.
\begin{zed}
    UStatus ::= uok | ufail
\end{zed}

The response from this program to the environment is a set of product identities of which the price is not updated successfully due to 1) no linked ESEL ID to the product or 2) failed update to its linked ESEL. The first reason is given the status constant $NA$ and the second is provided the constructor $fail\ldata ESID \rdata$.
\begin{zed}
    % NA - no correponding ESEL ID for the product
    FStatus ::= fail \ldata ESID \rdata | NA
\end{zed}

Types for handling in CTOC
\begin{zed}
ESIDpfunPID == ESID \pfun PID
PIDpfunPrice == PID \pfun Price
PIDpfunpowerFStatus = PID \pfun \power~FStatus
PIDcrossFStatus = PID \cross FStatus
ESID \cross Price = ESID \cross Price
ESID \cross UStatus = ESID \cross UStatus
\end{zed}
Two channels are provided to update the map from ESEL ID to product ID. $updateallmap$ will clear all stored map and use the input map as new map, while $updatemap$ just updates a partial map. In this map, one ESEL can be linked to up to one product. However, one product may associate with multiple ESELs.
\begin{circus}
	\circchannel\ updateallmap: ESIDpfunPID \\
	\circchannel\ updatemap: ESIDpfunPID
\end{circus}

Similarly, two channels are provided to update the price information. $updateallprice$ will clear all price information and use the input price information as new price, while $updateprice$ just updates price partially.
\begin{circus}
	\circchannel\ updateallprice: PIDpfunPrice \\
	\circchannel\ updateprice: PIDpfunPrice
\end{circus}

The $update$ channel gives a signal to the program to start update process.
\begin{circus}
	\circchannel\ update
\end{circus}

The $failures$ channel returns all failed products and related error reasons after update. Since one product may associate with multiple displays, the return status is a power set of $FStatus$ to denote which specific displays that the product links are updated unsuccessfully. But it is worth noting that $NA$ and $fail$ must not occur in a product's return set at the same time because they can not be both no associate display and associate display update fail.
\begin{circus}
	\circchannel\ failures: PIDpfunpowerFStatus
\end{circus}

The internal $resp$ event is used to collect update responses from all displays and $terminate$ event is for completing the collection.
\begin{circus}
    % inside
	\circchannel\ resp: PIDcrossFStatus \\
    \circchannel\ terminate \\
    \circchannelset\ RespInterface == \lchanset resp, terminate \rchanset
\end{circus}

%The channels below are used to communicate between the server and gateways, or between gateway internals. The server uses $gupdateprice$ to send price information with ESEL IDs to the corresponding gateway, while $gfailure$ is used to get back the udpate result from the gateway.
%\begin{circus}
%    % price info to start a new update
%	\circchannel\ gupdateprice: GID \cross (ESID \pfun Price) \\
%    % update result response
%	\circchannel\ gfailure: GID \cross \power~ESID \\
%\end{circus}
%
%$gresp$ and $gterminate$ are used in the internal of gateways to collection update results from each ESEL and terminate after collection.
%\begin{circus}
%    % gateway internal response collection
%	\circchannel\ gresp: ESID \\
%	\circchannel\ gterminate \\
%    \circchannelset\ GRespInterface == \lchanset gresp, gterminate \rchanset
%\end{circus}

This $uupdate$ event is to update one ESEL to the specific price, and $ures$ for update response from this ESEL.
And $udisplay$ is used to synchronise the show of price on all ESELs at the same time and $finishdisplay$ is used to wait for display completion of all ESELs. That is the similar case for $uinit$ and $ufinishinit$ that are for initialisation synchronisation.
\begin{circus}
    % unit
	\circchannel\ uupdate: ESID \cross Price \\
	\circchannel\ ures: ESID \cross UStatus \\
	\circchannel\ uinit, finishuinit\\
	\circchannel\ udisplay, finishudisplay
\end{circus}

And $display$ is used to synchronise the show of price on all gateways (or ESELs) at the same time and $finishdisplay$ is used to wait for display completion of all gateways (or ESELs). That is the similar case for $init$ and $finishinit$ that are for initialisation synchronisation.
\begin{circus}
	\circchannel\ init, finishinit \\
	\circchannel\ display, finishdisplay
\end{circus}

The channels below are for communication between the ESEL system and displays. The $write$ event writes price to a display, and the $read$ event reads price from the display. $ondisplay$ turns on the related display and $offdisplay$ turns off it conversely.
\begin{circus}
	\circchannel\ write: ESID \cross Price \\
	\circchannel\ read: ESID \cross Price \\
	\circchannel\ ondisplay: ESID \\
	\circchannel\ offdisplay: ESID
\end{circus}


\paragraph{Controller Process}
The process for overall control of the system, named $Controller$, is defined as an explicitly defined process.

\begin{circus}
	\circprocess\ Controller \circdef \circbegin \\
% \end{circus}
%
% $Controller$ has three state components: $pumap$ for mapping from displays to products, $ppmap$ for mapping from products to their price, and $response$ for the response of one update to the environment.
% \begin{circusaction}
    	\circstate\ State \defs [ pumap: ESID \pfun PID; ppmap: PID \pfun Price; response: PID \pfun (\power~FStatus) ]
% \end{circusaction}
% Initially, these three state components all are empty.
% \begin{zed}
    	\t1	Init \circdef (((pumap := \emptyset) \circseq (ppmap := \emptyset)) \circseq (response := \emptyset))
% \end{zed}
% The $UpdateMap$ schema updates part of the displays to products map according to the input map, while the $UpdateAllMap$ schema discards stored map and uses new input map as $pumap$.
% \begin{zed}
        \t1 UpdateMap \circdef (pumap := pumap \oplus map)\\
        \t1 UpdateAllMap \circdef (pumap := map)
% \end{zed}
% The $NewPrice$ updates part of price information stored, while the $AllNewPrice$ discards all price information stored and uses input price as $ppmap$.
% \begin{zed}
        \t1 NewPrice \circdef (ppmap := ppmap \oplus price)\\
        \t1 AllNewPrice \circdef (ppmap := price)\\
% \end{zed}
% $AUpdatemap$ is an action defined to update displays to products map: either partial update by $updatemap$ event or complete update by $updateallmap$ event.
% \begin{circusaction}
        \t1 AUpdatemap \circdef updatemap?map \then UpdateMap  \extchoice updateallmap?map \then UpdateAllMap \\
% \end{circusaction}
% Similarly, $ANewPrice$ is an action defined to update products to price map: either partial update by $updateprice$ event or complete update by $updateallprice$ event.
% \begin{circusaction}
        \t1 ANewPrice \circdef updateprice?price \then NewPrice \\
            \t2 \extchoice updateallprice?price \then AllNewPrice \\
% \end{circusaction}
% A parameterised action, $AUpdateUnitPrice$, is given to update the price (specified by the formal $pid$ parameter) to a  display (given by the formal $uid$ parameter). It sends the price to the specified display by the $write$ event, and then read back the price from the display by the $read$ event. If the write price matchs with the read price, then the update is successful. Otherwise, it fails ($ufail$) and sends the result to response collection action $CollectResp$ below, then terminates.
% \begin{circusaction}
        %
        \t1 AUpdateUnitPrice \circdef uid:ESID; pid:PID \circspot \\
            \t2 write.uid.(ppmap~pid) \then read.uid?y \then \\
            \t2 (\lcircguard y = (ppmap~pid) \rcircguard \circguard \Skip \\
            \t2 \extchoice \lcircguard y \neq (ppmap~pid) \rcircguard \circguard resp.pid.(fail~uid) \then \Skip) \\
% \end{circusaction}
% The parameterised action $AUpdateProductUnits$ aims to update one product's price specified by the formal $pid$ parameter in case the product has associated displays. Since one product may have more than one associated displays, this action updates the product's price to all associated displays. Furthermore, the update to each display is independent. Therefore, they are combined together into an interleave. It is worth noting that each $AUpdateUnitPrice$ action will not update state or local variables and thus its name set is empty.
% \begin{circusaction}
%        %
        \t1 AUpdateProductUnits \circdef pid:PID \circspot \\
            \t2 (\Interleave uid: (\dom~(pumap \rres \{pid\}))  \circspot AUpdateUnitPrice(uid, pid)) \\
% \end{circusaction}
% Otherwise, if the product has not been allocated the corresponding displays, it sends back a response to state this error $NA$. The behaviour is defined in the $AUpdateNoUnit$ action.
% \begin{circusaction}
        \t1 AUpdateNoUnit \circdef  pid:PID \circspot resp.pid.NA \then \Skip \\
% \end{circusaction}
%
% The behaviour of the price update for a product given in $pid$ is the update of product either with associated displays, guarded $AUpdateProductUnits$, or without associated displays, guarded $AUpdateNoUnit$.
% \begin{circusaction}
        \t1 AUpdateProduct \circdef pid:PID \circspot \\
            \t2 \,\,\,\, \lcircguard pid \in \ran~pumap \rcircguard \circguard AUpdateProductUnits(pid) \\
            \t2 \extchoice \lcircguard pid \notin \ran~pumap \rcircguard \circguard AUpdateNoUnit(pid) \\
% \end{circusaction}
%
% Then the update of all products is given in the action $AUpdateProducts$. At first, it is an interleave of all updates of the products which have associated price, then follows a $terminate$ event to finish the update.
% \begin{circusaction}
        \t1 AUpdateProducts \circdef ((\Interleave pid: (\dom~ppmap) \circspot AUpdateProduct(pid)) \circseq (terminate \then \Skip)) \\
% \end{circusaction}
%
% The $AddOneFailure$ schema adds one failure (either update failure or no associate failure) for a product to the state component $response$.
% \begin{zed}
    \t1 AddOneFailure \circdef
        \t2 (\lcircguard (pid \in \dom~response) \rcircguard \circguard \\
            \t3 (response := (response \oplus \{pid \mapsto (response(pid) \cup \{fst\}) \}))) \circseq \\
        \t2 (\lcircguard (pid \notin \dom~response)  \rcircguard \circguard \\
            \t3 (response := (response \cup \{pid \mapsto \{fst\} \})))\\
% \end{zed}
%
% The $CollectResp$ action is to collect responses from all units and write them into the $response$ variable by $AddOneFailure$ schema expression. It recursively waits for the response from the units, or terminates if required.
% \begin{circusaction}
        \t1 CollectResp \circdef \circmu muX \circspot \\
            %\t2 (resp?pid?fst \then response := response \oplus \{pid \mapsto fst \} \circseq X) \\
            \t2 (((resp?pid?fst \then AddOneFailure) \circseq muX) \extchoice terminate \then \Skip) \\
% \end{circusaction}
%
% Then update of all products and response collection behaviours are put together into $AUpdateResp$ action. It is a parallel composition of $AUpdateProducts$ and $CollectResp$ actions and they are synchronised with $resp$ and $terminate$ events. Furthermore, the left action $AUpdateProducts$ will not update state variables (its name set is empty set) while the right action $CollectResp$ will update $response$ (its name set has only one variable $response$). Finally, these internal events are hidden.
% \begin{circusaction}
        \t1 AUpdateResp \circdef \\
        \t2 ((AUpdateProducts \lpar \emptyset | RespInterface | \{ response \} \rpar CollectResp ) \\
        \t2 \circhide RespInterface) \\
% \end{circusaction}
%
% All displays will synchronise on $display$ event to show the price at the same time, which is defined in $ADisplay$. Whether a display should be turned on or off is decided based on the logic below.
% \begin{itemize}
%     \item If the display is not mapped to a product, then turn it off.
%     \item Otherwise, if the display linked product is not to be updated, then turn it off.
%     \item Otherwise, if the display has been written the price successfully, then turn it on.
%     \item Otherwise, then turn it off.
% \end{itemize}
%
% \begin{circusaction}
        \t1 ADisplay \circdef \\
        \t2 ((\lpar \lchanset display \rchanset \rpar uid: ESID \circspot \lpar \emptyset \rpar display \then ( \\
        \t3 \circif\ uid \notin \dom~pumap \circthen offdisplay.uid \then \Skip\\
        \t3 \circelse\ uid \in \dom~pumap \circthen \\
            \t4 \circif\ pumap(uid) \notin \dom~ppmap \circthen offdisplay.uid \then \Skip\\
            \t4 \circelse\ pumap(uid) \in \dom~ppmap \circthen \\
                \t5 \circif\ pumap(uid) \notin \dom~response \circthen \\
                    \t6 ondisplay.uid \then \Skip\\
                \t5 \circelse\ pumap(uid) \in \dom~response \circthen \\
                    \t6 \circif\ (fail~uid) \notin response(pumap(uid)) \circthen \\
                    \t7 ondisplay.uid \then \Skip\\
                    \t6 \circelse\ (fail~uid) \in response(pumap(uid)) \circthen \\
                    \t7 offdisplay.uid \then \Skip \\
                    \t6 \circfi \\
                \t5 \circfi \\
            \t4 \circfi \\
        \t3 \circfi \\
        \t2 )) \circhide \lchanset display \rchanset) \\
%        \t3 \lcircguard uid \notin \dom~pumap \rcircguard \circguard offdisplay.uid \then \Skip\\
%        \t3 \extchoice \lcircguard uid \in \dom~pumap \land pumap(uid) \notin \dom~ppmap \rcircguard \circguard \\
%        \t4 offdisplay.uid \then \Skip\\
%        \t3 \extchoice \lcircguard uid \in \dom~pumap \land pumap(uid) \notin \dom~response \rcircguard \circguard \\
%        \t4 ondisplay.uid \then \Skip\\
%        \t3 \extchoice \lcircguard uid \in \dom~pumap \land pumap(uid) \in \dom~response \land \\
%        \t4 (fail~uid) \notin response(pumap(uid)) \rcircguard \circguard ondisplay.uid \then \Skip\\
%        \t3 \extchoice \lcircguard uid \in \dom~pumap \land pumap(uid) \in \dom~response \land \\
%        \t4 (fail~uid) \in response(pumap(uid)) \rcircguard \circguard offdisplay.uid \then \Skip\\
%        \t2 )) \circhide \lchanset display \rchanset \\
%        \t1 ADisplay \circdef ((\lpar \lchanset display \rchanset \rpar uid: ESID \circspot \lpar \emptyset \rpar display \then ondisplay.uid \then \Skip) \\
%        \t2 \lpar \emptyset | \lchanset display \rchanset | \emptyset \rpar (display \then \Skip)) \\
%        \t2 \circhide \lchanset display \rchanset \\
% \end{circusaction}
%
% The overall price update action is given in $AUpdatePrice$, which accepts a $update$ event from its environment, then clears $response$, updates the price, sends $display$ event to make all ESELs show their price at the same time, then feeds back the response to the environment.
% \begin{circusaction}
        \t1 AUpdatePrice \circdef ((((update \then (response := \emptyset)) \circseq \\
            \t2 AUpdateResp) \circseq ADisplay) \circseq (failures.response \then \Skip)) \\
% \end{circusaction}
%
% Initially, state components are cleared and all displays are turned off.
% \begin{circusaction}
    \t1 AInit \circdef Init \circseq (\Interleave u: ESID  \circspot offdisplay.u \then \Skip) \\
% \end{circusaction}
%
% The overall behaviour of the $Controller$ process is given by its main action. It initializes at first, then repeatedly provides display map update, price map, or price update to its environment.
% \begin{circusaction}
	\t1 \circspot AInit \circseq (\circmu X \circspot (AUpdatemap \extchoice ANewPrice \extchoice AUpdatePrice) \circseq X) \\
% \end{circusaction}
%
% \begin{circus}
	\circend
\end{circus}

\paragraph{System}
The ESEL Specification is simply the $Controller$ process.
\begin{circus}
    \circprocess\ ESELSpec \circdef  Controller
\end{circus}
