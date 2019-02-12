\documentclass[a4paper,11pt]{scrartcl}

%include polycode.fmt
%include spacing.fmt
%if style /= newcode
%subst newline = "\nextline'n"
%subst blankline = "\nextline[1ex]'n"
%endif

\usepackage{iohk}
\usepackage{mathpazo}
\usepackage{semantic}
\usepackage{hyperref}
% for UML
\usepackage{tikz}
\usetikzlibrary{automata, positioning, arrows}
\usepackage{pgf-umlsd}
%\usepgflibrary{arrows} % for pgf-umlsd
\usepackage{verbatim}
% for ld
\usepackage{bussproofs}

\usetikzlibrary{calc,positioning,arrows}

\tikzset{
    ->, % makes the edges directed
    >=stealth', % makes the arrow heads bold
    node distance=3cm, % specifies the minimum distance between two nodes. Change if necessary.
    every state/.style={thick, fill=gray!10}, % sets the properties for each ’state’ node
    initial text=$Start$, % sets the text that appears on the start arrow
    }

% The following is the general setup of the machinery. As this
% gets longer, it's probably useful to extract this into its own
% fmt file.
%
% There are some helpful TeX macros, but primarily we do formatting
% tricks via formatting directives. Several of these have different
% expansions depending on whether we extract code (in "newcode" mode)
% or TeX (in "poly" mode).

\newcommand\named[1]{\mathsf{#1}}
\renewcommand\Conid[1]{\mathsf{#1}}
\renewcommand\Varid[1]{\mathit{#1}}

%if style /= newcode
%format :: = "\in"
%format List a = a "^{*}"
%format Pair (a) (b) = a "\times " b
%format Set = "\mathbb{P}"
%format `from` = "\in"
%format `Set.from` = "\in"
%format `List.from` = "\in"
%format (Set.singleton (x)) = "\{" x "\}"
%format `Map.union` = "\cup "
%format `Set.union` = "\cup "
%format Map.! = ^^
%format Set.empty = "\emptyset"
%format keysSet = "\dom "
%format `isSubsetOf` = "\subseteq "
%format |-> = "\mapsto"
%format /= = "\neq "
%format == = "="
%format `implies` = "\Rightarrow "
%format restrictDom (x) (y) = x "\vartriangleleft " y
%format subtractDom (x) (y) = x "\ntriangleleft " y
%format SET (x) (y) = "\left\{" x "\middle|" y "\right\}"
%format SET' (x) (y) = "\left\{" x "\middle|" y "\right\}"
%format SUM (x) (y) = "\sum\limits_{" x "}" y
%format ALL (x) (y) = "\forall " x ", " y
%format VSTACK (x) (y) = "\begin{array}{l}" x "\cr " y "\end{array}"
%format LET x = x
%format Relation3 (a) (b) (c) = Set (a `Pair` b `Pair` c)
%format Relation4 (a) (b) (c) (d) = Set (a `Pair` b `Pair` c `Pair` d)
%format (serialised (a)) = "\llbracket" a "\rrbracket"
%format GUARDED =
%format AND     =
%format WITHGUARDED =
%else
%format SET (x) (y) = "Map.fromList [ " x " | " y "]"
%format SET' (x) (y) = "Set.fromList [ " x " | " y "]"
%format SUM (x) (y) = "sum [ " y " | " x "]"
%format ALL (x) (y) = "and [ " y " | " x "]"
%format dcerts = "dcerts "
%format `from` = " <- Map.toList $ "
%format `Set.from` = " <- Set.toList $ "
%format `List.from` = " <- "
%format |-> = "`Pair`"
%format VSTACK (x) (y) = x ", " y
%format LET x = "let " x
%format Relation3 (a) (b) (c) = a -> b -> c -> Bool
%format Relation4 (a) (b) (c) (d) = a -> b -> c -> d -> Bool
%format GUARDED = "guarded :: Bool; guarded = "
%format AND     = " && "
%format WITHGUARDED = " && guarded"
%endif

% The following is the module header and some basic definitions
% needed for the demo, to be included only in the code, but not
% currently in the LaTeX output.
%
% Very few of the definitions are also added to help the formatting,
% such as the Pair type and pattern synonym.

%if style == newcode

> {-# LANGUAGE PatternSynonyms #-}
> {-# LANGUAGE StandaloneDeriving #-}
> {-# OPTIONS_GHC -Wno-missing-methods #-}
> module CardanoShellSpec where
>
> import Data.Map as Map
> import Data.Set as Set
>
> type List a = [a]
> type Pair a b = (a, b)
> pattern Pair x y = (x, y)

> implies :: Bool -> Bool -> Bool
> x `implies` y = not x || y
> infixr 1 `implies`

> data ServerMessage 
>    = QueryPort
>    | Ping

> instance Eq ServerMessage
> instance Ord ServerMessage

> data ClientMessage 
>    = Started
>    | Pong
>    | ReplyPort Word16

> instance Eq ClientMessage
> instance Ord ClientMessage

%endif

% The following are some more specific formatting directives.
% The spec code currently formats top-level functions differently
% from local names / arguments, so we have formatting directives
% for each of these top-level functions, which only apply when
% producing LaTeX output.

%if style /= newcode
%format fullProtocol = "\named{fullProtocol}"
%endif

\begin{document}

\title{Specification of the Cardano shell}

\author{Kristijan Šarić}

\date{06.02.2019}

\maketitle

\begin{abstract}
This document is a high-level specification of how the pieces that make Cardano shell work together and an attempt to define a general, secure and simple way to combine them, while introducing the reader with the specifics of how they work.
\textit{Beware, work in progress!}
\end{abstract}

\tableofcontents
\listoffigures
\listoftables

\newpage
\section{Introduction}
\label{sec:introduction}

The introduction. WIP!

\newpage 
\section{IPC and communication between Daedalus and Node}
\label{sec:ipc}

Currently, the \textit{Daedalus} and the \textit{Node} (this is what I'm calling the node, thus the uppercase) communicate via \textbf{IPC for reaching a consensus which port to use for the JSON API communication, since we have a lot of issues of ports being used} .
\textbf{IPC} (Inter Process Communication) is a set of methods which processes can use to communicate - \url{https://en.wikipedia.org/wiki/Inter-process_communication}.\\

The actual communication right now is being done by the \textit{spawn} function, pieces of which can be found \href{https://github.com/nodejs/node/blob/62942e9ad7a59b76e9255ea2560bad2245709efc/lib/internal/child_process.js#L306}{here}.
The part of the code which adds the handle id which they will use to communicate via environment variable "NODE\_CHANNEL\_FD" \href{https://github.com/nodejs/node/blob/master/lib/internal/child_process.js#L324-L335}{here}.\\

Currently, the \textit{Deadalus} starts the \textit{Node} (we will ignore the \textit{Launcher} for now, since it complicates the story a bit).\\

The initial simplified communication protocol can be seen on Figure ~\ref{fig:ipcSimpleFig}.\\

When the \textit{Daedalus} calls and starts the \textit{Node}, it also opens up the \textbf{IPC} protocol to enable communication between the two.
First, the \textit{Node} sends the message \textbf{Started} back to the \textit{Daedalus} to inform him that the communcation can begin.
After that, \textit{Daedalus} sends the message \textbf{QueryPort} to the \textit{Node}, and the \textit{Node} responds with the free port it found using \textbf{ReplyPort PORTNUM} that is going to be used for starting the HTTP "server" serving the \textit{JSON API} which they can then use to communicate further.\\

Since the communication is bi-directional, currently the communication is using \textbf{files}.\\

We can easily generalize this concept. We can say that \textit{Daedalus} is the \textit{Server}, and that the \textit{Node} is the \textit{Client}. Since the communication is bi-directional, we can say that either way, but we can presume that the \textit{Server} is the process which is started first.

What does this bring us? It brings us the ability to \textbf{decouple} our implementation from the specific setting where \textit{Daedalus} is the \textit{Server} and the \textit{Node} is the \textit{Client}. There are some ideas that we might switch the order of the way we currently run these two, so we can freely implement that either way. For example, when we write tests for this communication protocol, we need to both start the server and the client and then check their interaction. It also removes any extra information that we might need to drop anyway. What we are focusing here is the \textbf{communication protocol} and not it's actors. We don't really care who says to whom, we are interested in seeing what is being said - \textit{how the whole protocol works}.

% http://www.texample.net/tikz/examples/pgf-umlsd/
\begin{figure}[ht]
  \centering

  \begin{sequencediagram}
    \newthread{ss}{Daedalus}{Daedalus}
    \newinst{nd}{Node}{Node}

    \postlevel
    \begin{call}{ss}{Run node}{nd}{Node started}
    \end{call}

    \postlevel
    \begin{callself}{ss}{Start IPC}{}
    \end{callself}
    
    \postlevel
    \begin{call}{ss}{What is your port number?}{nd}{Node port number}
    \end{call}

  \end{sequencediagram}

  \caption{Message protocol for current IPC implementation.}
  \label{fig:ipcSimpleFig}
\end{figure}

\newpage 
\subsection{IPC simple communication}
\label{sec:ipcSimple}

Here we will take a look at the simplest possible communication. \textbf{Ping} and \textbf{Pong}. The \textit{Server} sends the \textbf{Ping} and the \textit{Client} responds with a \textbf{Pong}.\\

We can take a look at this very simple protocol on Figure ~\ref{fig:ipcPingPongFig}.\\

\begin{figure}[ht]
  \centering

  \begin{sequencediagram}
    \newthread{se}{Server}{Server}
    \newinst{cl}{Client}{Client}

    \postlevel
    \begin{call}{se}{Ping}{cl}{Pong}
    \end{call}

  \end{sequencediagram}

  \caption{IPC message protocol for Ping/Pong.}
  \label{fig:ipcPingPongFig}
\end{figure}

Very simple transformation rules can be applied here.

\begin{equation}
    Ping \Longrightarrow Pong
\end{equation}

\begin{equation}
    \label{eq:ping-pong-ipc}
    \AxiomC{Ping}
    \UnaryInfC{Pong}
    \DisplayProof
\end{equation}

And that's it. Let's now take a look at a more involved case where we care about exceptional situations.

\newpage 
\subsection{IPC simple communication with exceptions}
\label{sec:ipcSimpleExceptions}

Here we will take a look at the simplest possible communication. \textbf{Ping} and \textbf{Pong}. The \textit{Server} sends the \textbf{Ping} and the \textit{Client} responds with a \textbf{Pong}. We also consider all the \textbf{exceptional situations}.\\

What can go wrong when we send the message? For example, we need to consider what actor are we currently looking at. Is it the \textit{Client} or the \textit{Server}? The socket could be closed, the process could be shut down, the message could take too long to respond, the format could be wrong (yay, types) and so on. Since we are not interested in the low-level details, we can generalize these exceptional situations into more general messages that we can enumerate.\\

We can simplify all of this by saying there is an exception \textit{MessageSendFailure} that can be used on \textbf{both sides}. This simplifies a lot of things for us, including different exceptional situations we might reach. The result can be seen here.

\begin{equation}
    (Ping \wedge \neg MessageSendFailure) \Longrightarrow Pong
\end{equation}

\begin{equation}
    \AxiomC{$Ping$}
    \AxiomC{}
    \UnaryInfC{$\neg MessageSendFailure$}
    \BinaryInfC{$Pong$}
    \DisplayProof
\end{equation}

The other situation just halts the protocol, which we can observe as bottom.

\begin{equation}
    \label{eq:ping-pong-ipc-bottom}
    \AxiomC{MessageSendFailure}
    \UnaryInfC{$\bot$}
    \DisplayProof
\end{equation}


And this is a simplified way we can observe any exception situation in this communication.

\newpage 
\subsection{IPC protocol communication with exceptions}
\label{sec:ipcProtocol}

Here we will take a look at a more complex communication where we actually have the full communication between parties - \textit{Server} and \textit{Client}.

When the communication starts, the \textit{Client} sends the \textbf{Started} message to the \textit{Server} indicating that it's now ready for the communication.
After that, the \textit{Server} sends the \textbf{QueryPort} message, which is then sent to the \textit{Client} where the \textit{Client} selects over which port will the \textit{REST JSON} communication continue using \textbf{ReplyPort PORT}.

What can go wrong when we send the message? The same thing as in the previous section.

We can simplify all of this by saying there is an exception \textit{MessageSendFailure} that can be used on both sides. This simplifies a lot of things for us, including different exceptional situations we might reach. The result can be seen here.

\begin{equation}
    Ping \wedge \neg MessageSendFailure \Longrightarrow Pong
\end{equation}

\begin{equation}
    Started \wedge QueryPort \wedge \neg MessageSendFailure \Longrightarrow ReplyPort
\end{equation}

The other situation just halts the protocol, which we can observe as bottom.

\begin{equation}
    \AxiomC{$Ping$}
    \AxiomC{}
    \UnaryInfC{$\neg MessageSendFailure$}
    \BinaryInfC{$Pong$}
    \DisplayProof
\end{equation}

\begin{equation}
    \label{eq:protocol-ipc-queryport}
    \AxiomC{$Started$}
    \UnaryInfC{$QueryPort$}
    \AxiomC{}
    \UnaryInfC{$\neg MessageSendFailure$}   
    \BinaryInfC{$ReplyPort \{ \textbf{port} \mid port < 65535 \wedge port > 0 \}$}
    \DisplayProof
\end{equation}

\begin{equation}
    \label{eq:protocol-ipc-bottom}
    \AxiomC{MessageSendFailure}
    \UnaryInfC{$\bot$}
    \DisplayProof
\end{equation}

And that is our full communication protocol. It can be seen on Figure ~\ref{fig:ipcFullProtocolFig}.\\

The state machine diagram that can be used to represent this can be seen here.\\

\begin{figure}[ht] % ’ht’ tells LaTeX to place the figure ’here’ or at the top of the page
    \centering % centers the figure
    \begin{tikzpicture}
        \node[state, accepting, initial] (q1) {$Started$};
        \node[state, right of=q1] (q2) {$Ping$};
        \node[state, accepting, right of=q2] (q3) {$Pong$};
        \node[state, below of=q1] (q4) {$QueryPort$};
        \node[state, accepting, right of=q4] (q5) {$ReplyPort$};
        \draw 
            (q1) edge[above] node{} (q2)
            (q2) edge[above] node{} (q3)
            (q3) edge[bend left, below] node{} (q1) %return
            %(q3) edge[bend left, below] node{} (q2)
            (q1) edge[below] node{} (q4)
            (q4) edge[below] node{} (q5)
            (q5) edge[below] node{} (q1); %return
    \end{tikzpicture}
    \caption{Full protocol FSM.}
    \label{fig:my_label}
\end{figure}

% http://www.texample.net/tikz/examples/pgf-umlsd/
\begin{figure}[ht]
  \centering

  \begin{sequencediagram}
    \newthread{se}{Server}{Server}
    \newinst{cl}{Client}{Client}

    \postlevel
    \begin{call}{cl}{Started}{se}{}
    \end{call}

    \postlevel
    \begin{call}{se}{QueryPort}{cl}{ReplyPort PORT}
    \end{call}
    
  \end{sequencediagram}

  \caption{Message protocol for the full IPC implementation.}
  \label{fig:ipcFullProtocolFig}
\end{figure}

We can then consider a simple transition function for the client.

% https://github.com/input-output-hk/fm-ledger-rules/pull/108/files

> fullProtocol :: ServerMessage -> ClientMessage
> fullProtocol Ping       =  Pong
> fullProtocol QueryPort  =  ReplyPort 0


\newpage
\newpage 
\section{Update mechanism}
\label{sec:update}

% https://tex.stackexchange.com/questions/207240/drawing-simple-sequence-diagram/209079

First of all, we need to understand that the blocks in the blockchain contain the version of \textit{Daedalus} (the frontend).
We can imagine that each block can contain a version of the frontend, which is essentially a hash signature from the installer. That is something that can change in the future, but we can simplify our life by imagining that what the blockchain contains is the link for the installer (which, when simplified, it does).

Let's start simple. Let's take the blockchain and the version into consideration.

\begin{tikzpicture}[node distance=2cm,auto,>=stealth']

\node[] (server) {server};
\node[left = of server] (client) {client};
\node[below of=server, node distance=5cm] (server_ground) {};
\node[below of=client, node distance=5cm] (client_ground) {};
%
\draw (client) -- (client_ground);
\draw (server) -- (server_ground);
\draw[->] ($(client)!0.25!(client_ground)$) -- node[above,scale=1,midway]{Text} ($(server)!0.25!(server_ground)$);
\draw[<-] ($(client)!0.35!(client_ground)$) -- node[below,scale=1,midway]{Hey} ($(server)!0.35!(server_ground)$);

\end{tikzpicture}

Let's see how that looks like:


\end{document}
