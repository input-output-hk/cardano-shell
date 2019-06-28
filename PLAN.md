# Milestone planning

(see [Github milestones](https://github.com/input-output-hk/cardano-shell/milestones?direction=asc&sort=title&state=open))

|     | Id  | depends on | title | description | deliverable |
|-----|-----|------------|-------|-------------|-------------|
| [_] | [**NOD001**](https://github.com/input-output-hk/cardano-shell/milestone/7) |  | Daedalus IPC complete  | Inter process communication, Daedalus uses this to perform initial configuration agreements between wallet and also for clean shutdowns (node or wallet). Wallet team needs this in order to communicate with Daedalus - full Daedalus integration  | IPC implementation and documentation |
| [_] | E1.1   |        | IPC implementation |  | IPC implementation |
| [_] | T1.1.1 |  | Requirements for integration | from Wallet BE team; from existing solution | requirements |
| [_] | T1.1.2 | T1.1.1 | Support for integration | to Wallet BE team | integration complete |
| [x] | E1.2   | T1.1.2 | QuickCheck state machine tests |  | Tests for IPC |
| [x] | T1.2.1 |  | QuickCheck state machine tests | needs state machine tests |  |
| [x] | E1.3   | T1.2.1 | Documentation |  | Documentation |
| [x] | T1.3.1 |  | Documentation |  |  |

|     | Id  | depends on | title | description | deliverable |
|-----|-----|------------|-------|-------------|-------------|
| [x] | [**NOD002**](https://github.com/input-output-hk/cardano-shell/milestone/8) |  | Configuration complete for batch mode block validation  | Prove that the cofiguration system is valid for the needs. This is a design (configuration subsystem in node shell) validation point. (25/03 - Dev is in progress). Could be demoed if compelte.  | Valid configuration for batch mode block validation |
| [x] | T2.1.1 |  | Assist ledger team with integration (#46) | dependency: cardano-ledger | cardano-ledger integrated with cardano-shell |

|     | Id  | depends on | title | description | deliverable |
|-----|-----|------------|-------|-------------|-------------|
| [_] | [**NOD003**](https://github.com/input-output-hk/cardano-shell/milestone/9) |  | Node shell as a library | "Design validation for features, configuration and is used for wallet and node 
(useable for more than one applications) " | Node shell as library |
| [_] | T3.1.1 |  | requirements gathering: wallet BE, ledger team | if they pop up | requirements |
| [_] | T3.1.2 | T3.1.1 | QuickCheck state machine tests | needs state machine tests | Test for shell |
| [_] | T3.1.3 | T3.1.1 | Redesign modules, define API | only expose functions, types in API | cardano-shell as a library |
| [x] | T3.1.4 | T3.1.3 | Documentation |  | Documentation for the shell |

|     | Id  | depends on | title | description | deliverable |
|-----|-----|------------|-------|-------------|-------------|
| [_] | [**NOD004**](https://github.com/input-output-hk/cardano-shell/milestone/10) | NOD003 | Miminal integration with wallet BE - Wallet BE team & Node Shell  | No Daedalus IPC, minimal logging output, partial configuration is complete, completed features framework  | wallet BE integrated with shell |
| [_] | E4.1   |  | Assist with integration | dependency: cardano-wallet | cardano-wallet integrated with shell |
| [_] | T4.1.1 |  | Assist with integration (#78) | dependency: cardano-wallet |  |

|     | Id  | depends on | title | description | deliverable |
|-----|-----|------------|-------|-------------|-------------|
| [_] | [**NOD005**](https://github.com/input-output-hk/cardano-shell/milestone/11) | NOD002, NOD003 | Minimal integration with Node - Ledger, Consensus & Node Shell | No Daedalus IPC, minimal logging output, partial configuration is complete, completed features framework  | Ledger, consensus integrated with node shell |
| [_] | E5.1   |  | Assist with integration |  |  |
| [x] | T5.1.1 |  | Assist with integration | dependency: cardano-ledger |  |
| [_] | T5.1.2 |  | Assist with integration | dependency: consensus |  |
| [_] | T5.1.3 |  | Assist with integration | dependency: network |  |

|     | Id  | depends on | title | description | deliverable |
|-----|-----|------------|-------|-------------|-------------|
| [_] | [**NOD006**](https://github.com/input-output-hk/cardano-shell/milestone/12) | NOD004 | Maximum integration with wallet BE - Wallet BE team & Node Shell  | Minimal + full configuration, full logging coverage for components  | Working Wallet backend that is being run by Node Shell |
| [_] | E6.1   |  | Requirements |  |  |
| [_] | T6.1.1 |  | Requirements |  | The specification what the wallet team needs |
| [_] | E6.2   | T6.1.1 | Integration |  | Working wallet backend that is being run by Node Shell |
| [_] | T6.2.1 |  | Integrating required configuration |  | Configuration that the Wallet BE needs |
| [_] | T6.2.2 |  | Integrating required launcher functionality |  | Launcher options that the Wallet BE needs |
| [_] | E6.3   | T6.2.2 | QA Testing |  | Tested working wallet with backend |
| [_] | T6.3.1 |  | Testing configuration |  | Correect configuration that the Wallet BE needs |
| [_] | T6.3.2 |  | Testing launcher functionality |  | Correct launcher options that the Wallet BE needs |

|     | Id  | depends on | title | description | deliverable |
|-----|-----|------------|-------|-------------|-------------|
| [_] | [**NOD007**](https://github.com/input-output-hk/cardano-shell/milestone/13) | NOD005 | Maximum integration with Node - Ledger, Consensus & Node Shell | Minimal + full configuration, full logging coverage for components for node  | Working Ledger that is being run by Node Shell |
| [_] | E7.1   |  | Requirements |  |  |
| [_] | T7.1.1 |  | Requirements |  | The specification what the ledger team needs |
| [_] | E7.2   | T7.1.1 | Integration |  | Working Ledger that is being run by Node Shell |
| [_] | T7.2.1 |  | Integrating required configuration |  | Configuration that the Ledger needs |
| [_] | T7.2.2 |  | Integrating required launcher functionality |  | Launcher options that the Ledger needs |
| [_] | E7.3   | E7.2 | QA Testing |  | Tested working wallet with ledger |
| [_] | T7.3.1 |  | Testing configuration |  | Correect configuration that the ledger needs |
| [_] | T7.3.2 |  | Testing launcher functionality |  | Correct launcher options that the ledger needs |

|     | Id  | depends on | title | description | deliverable |
|-----|-----|------------|-------|-------------|-------------|
| [_] | [**NOD008**](https://github.com/input-output-hk/cardano-shell/milestone/14) | NOD006, NOD007 | Integration with 'Update system' - with Daedalus, Wallet BE & Node. Launcher and update mechansim complete  | Launcher now functions with rest of the 'update system'.  Launcher component which is used as part of the 'update system' - cross cutting across all major components | Full wallet/node working. Update system that returns and installs updates and fully working Daedalus with Wallet, and Node on the other side. |
| [_] | E8.1   |  | Launcher update system impl. (#50, but this is slightly ill-defined as this was created when I thought that the launcher's main part is the update system. It isn't.) | The update system implementation | The update system which can update the version of the wallet/node |
| [_] | T8.1.1 |  | Requirements |  |  |
| [_] | T8.1.2 |  | Documentation (#57) |  |  |
| [_] | E8.2   | T8.1.1 | QuickCheck state machine tests |  | Tests for update system |
| [_] | T8.2.1 |  | QuickCheck state machine tests | needs state machine tests |  |
| [_] | E8.3   | T8.1.1 | Initial implementation |  | The initial version of the update system |
| [_] | T8.3.1 |  | Implementation of the update system |  |  |
| [_] | E8.4   | T8.3.1 | Integration launcher, Daedalus |  | Fully working wallet and node |
| [_] | T8.4.1 |  | Integration of Daedalus and launcher |  |  |
| [_] | E8.5   | T8.3.1 | Integration launcher, wallet BE |  | Fully working wallet and node |
| [_] | T8.5.1 |  | Integration of Wallet BE and launcher |  |  |

|     | Id  | depends on | title | description | deliverable |
|-----|-----|------------|-------|-------------|-------------|
| [_] | [**NOD009**](https://github.com/input-output-hk/cardano-shell/milestone/15) | NOD008, NOD003, NOD001 | Formal methods, model verification (TLA+) | this milestone is not on the "critical path"; can be done after a release |  |
| [_] | E9.1   |  | Installation, get familiar |  |  |
| [_] | T9.1.1 |  | setup TLA+ locally, get familiar |  | TLA+ installation |
| [_] | E9.2   | E9.1 | TLA+ model of shell |  | TLA+ model of node-shell |
| [_] | T9.2.1 |  | find example, adapt to our needs |  | template/example |
| [_] | T9.2.2 |  | TLA+ model of shell |  | TLA+ model for shell |
| [_] | E9.3   | E9.1 | TLA+ model of IPC |  | TLA+ model for IPC |
| [_] | T9.3.1 |  | find example, adapt to our needs |  | template/example |
| [_] | T9.3.2 |  | complete IPC model |  | TLA+ model |
| [_] | E9.4   | E9.1 | TLA+ model of  launcher update system |  | TLA+ model of update system |
| [_] | T9.4.1 |  | find example, adapt to our needs |  | template/example |
| [_] | T9.4.2 |  | complete  launcher update system model |  | TLA+ model |
