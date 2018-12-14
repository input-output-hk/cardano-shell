# Architecture

The high level architecture that we need to have has to support many modules/features running in parallel (we fork a single thread _per-feature_ and then a _feature_ forks additional threads).
We can imagine we have several modules which are organized by their high-level responsibility and we call those modules, which are effectively code chunks grouped together, _features_.

## Features

Each _feature_ is responsible for a piece of code and has clearly defined responsibilities - we can imagine we have the following _features_:
- logging layer
- monitoring layer
- network layer
- blockchain layer
- ledger layer
- wallet (backend) layer

![cardano-shell-integration](https://user-images.githubusercontent.com/6264437/47286815-88df4100-d5f0-11e8-92a7-c807b6d3b47a.jpg)

And each of these _features_ have some dependencies, requires some configuration and produces an interface that the user (developer) can use.
For example, let's suppose we want to create a very simple logging/monitoring _feature_ (this example will have one _feature_ which combines both logging and monitoring, but they can be separate).

![logging_monitoring_deps](https://user-images.githubusercontent.com/6264437/48932225-fe457680-eefa-11e8-8aae-9764382e74ff.jpg)

We see that the _feature_ requires a specific *configuration and has some global exception handling*.
The specific configuration can be something really specific to logging, for example. We may need to read the default log level, whether it's info, debug, warn or something else - we need to define the level of information we want to save in the logs. For that, we require a specific configuration. That configuration is not part of the default configuration we usually parse when we start the _cardano-shell_ - when we parse the initial key configuration, we parse what *every feature requires*, not
something specific for each _feature_.
Then we have the _feature_ ready for usage and we can use the functions it contains. We will restrict this a bit later, but for now, let's suppose we can use all the functions in the module export.
And so, all is well. We are done! But wait! What about the other _features_? Ok, so I lied, we are not done. We need to able to communicate with the other nodes. What do we need for that? Networking! So we need to construct the _networking feature_. And what does networking use? It uses loggging! How does that look like?

![networking_deps](https://user-images.githubusercontent.com/6264437/48932488-84ae8800-eefc-11e8-89ff-5c8d45dc0f46.jpg)

Again we have a specific configuration for the _networking feature_ (for example the number of surrounding nodes we can communicate with?), we have some _global exception handling_, and we have a dependency! What is the dependency? It's the logging/monitoring (sorry for the confusion, I split them up here, since they really seem to be separate) _feature_.
And now we have constructed the _networking feature_! Are we done? NO! We can communicate with other nodes, but we don't have any blockchain logic running on the node. So we need to construct the _blockchain feature_. What are the dependencies for the _blockchain feature_? Logging, monitoring and networking. And again we have some specific configuration that we may need to read. In this case, it may be the number of blocks per epoch or epoch length or something else.

![blockchain_deps](https://user-images.githubusercontent.com/6264437/48932776-e0c5dc00-eefd-11e8-9701-b659cf44fcb7.jpg)

Are we done now? NO! But let's add just one more example, we can imagine stacking this up for quite some time. We need to construct the _ledger feature_ since we need a way to account for our balances and our transactions and a ton of other stuff. Again we might require logging, monitoring, networking (maybe at this level we might not need to call the _networking feature_ directly, but let's suppose that we do) and the blockchain. Again we have some _specific configuration_, for example the cost
of the transaction (or something that we use to calculate it), some _global exception handling_ and the dependencies. How does that look?

![ledger_dep](https://user-images.githubusercontent.com/6264437/48933094-4c5c7900-eeff-11e8-9cf9-6e4a04db182f.jpg)


Are we done now? NO!

## Layers

I lied before. It's not quite that simple. Let's go back to the beginning.

We need to be able to test this code easily. And that's harder than it sounds. When you are not building your code with testing in mind, it becomes very hard to actually test it. So we want to provide some interface towards the _features_ that we can stub out and replace with our test functions. We call those interfaces a _layer_. We then pass those interfaces around and when we want to replace them, we simply send the replaced interface around. We want to do that in order to *clearly separate the features and to enable us to test them in isolation*. I hope that makes sense, I don't want to write the explanation how testing works. A similar approach could be achieved by using a typeclass but it's not as nice. And this is not good just for testing. It's good for the project in general - we program towards interfaces and all the client needs to know about are the types and the interface. If we hide the type internals (directly or indirectly) we have a very nice way to build a maintainable project that can change it's behavior very quickly and the client won't be affected.
So let's draw some pictures here and make this a bit more clear. Let's simplify and say we will take a look at only three _features_ - logging, networking and blockchain.

![feature_layer_1](https://user-images.githubusercontent.com/6264437/48933434-89753b00-ef00-11e8-9edf-5f424caaba07.jpg)

When we complete the construction of this logging/monitoring _feature_, we get the initialized _layer_, which is the interface toward the _feature_. It's essentially a record of functions.
Let's make this a bit more concrete. Let's say we have an extremely simple interface for _logging_ and all we want our users (developers) to use is this:
```
logInfo     :: Text -> IO ()
logWarning  :: Text -> IO ()
logDebug    :: Text -> IO ()
```

![feature_layer_2](https://user-images.githubusercontent.com/6264437/48933544-ed97ff00-ef00-11e8-9d2f-349eaa2be225.jpg)

And we wrap this up in a data structure that is going to represent our interface.

![feature_layer_3](https://user-images.githubusercontent.com/6264437/48933604-32239a80-ef01-11e8-851e-44e437899f38.jpg)

So we wrapped our functions in an interface and when we pass it as a dependency to the next _feature_ we can always stub out the functions and see how the _feature_ behaves in isolation.
In a way, the produced *layer* is the _result of the feature_, and we can pass it down as a dependency to the next _feature_.

![feature_layer_4](https://user-images.githubusercontent.com/6264437/48933677-7f077100-ef01-11e8-8bf0-947b27de27f1.jpg)

We can imagine doing the same for the _networking feature_ - we construct a _feature layer_ that is the interface towards the _network feature_ and we pass it on as a dependency.

![feature_layer_5](https://user-images.githubusercontent.com/6264437/48933736-b24a0000-ef01-11e8-9da5-f148ee66e334.jpg)

And you shouldn't be shocked by the next image. What? They pass it as a dependency? Madness!

![feature_layer_6](https://user-images.githubusercontent.com/6264437/48933810-e9201600-ef01-11e8-87a8-a6a49213030e.jpg)

The only additional thing that you can see in the image is that we pass the _logging layer_ as another dependency as well. So now we can mock out both _features_ and use stubs for both.


Are we done now? NO!

I lied again. I simplified it a bit. If you take a look at the actual _layer_ example that we used, it uses _IO_. And are we going to use _IO_ on every function? I hope not. What can we do? Well we can keep the type parameter abstract and instantiate it to a proper set of effects later? Sounds like a great idea!

![feature_layer_abstract_effect](https://user-images.githubusercontent.com/6264437/48934055-db1ec500-ef02-11e8-910a-a11885661bb2.jpg)

In the example, we suppose that the interface is abstract (the `m` type is abstract) and we later on define it to be `forall m. (MonadIO m, MonadLog m) => m`, so an _mtl style effect_ which has two constraints on it - it can log and do IO, which sounds good. But there is nothing perfect and there are trade-offs everywhere. Even in our nice little example. How?
Let me show you. The abstract type is now constrained by two types - `MonadIO` and `MonadLog`.

![feature_layer_effect_escape_1](https://user-images.githubusercontent.com/6264437/48934364-fdfda900-ef03-11e8-8631-bcdb2f283eab.jpg)

So every function in that _layer_ must contain these two constraints. Why? Well because `m` in our example is the product type of all the effects of all the functions in a _layer_, right? If we change our `logDebug` function to contain, say `MonadState Text m` what can the other functions contain? Yes, they all _can_ contain state. We are allowing functions to use effects that we didn't intend -
isn't that one of the reasons we use Haskell in the first place? Even worse, seems all our functions are able to do _IO_, regardless of whether they actually need to use it!

![feature_layer_effect_escape_2](https://user-images.githubusercontent.com/6264437/48934561-d65b1080-ef04-11e8-808a-b83bee9a188b.jpg)

But that's not the worst part! The worst part is yet to come!
What happens when we use _logging layer_ in our _networking feature_ function?

![feature_layer_effect_escape_3](https://user-images.githubusercontent.com/6264437/48934599-fdb1dd80-ef04-11e8-984b-4d2f4cc2eef2.jpg)

Yes, now that function must infer the constraints. And if we use logging in one of our functions in the _networking layer_, what do we get? Yes, _IO_ in all the functions, since we unify all the constrains under one abstract type parameter `m`. And if the _blockchain feature_ uses the _networking layer_?

![feature_layer_effect_escape_4](https://user-images.githubusercontent.com/6264437/48934692-626d3800-ef05-11e8-98f5-ae7b10b8b597.jpg)

It's spreading! All over our codebase! And if, say, _networking layer_ has more constraints (which probably has), what happens?

![feature_layer_effect_escape_5](https://user-images.githubusercontent.com/6264437/48934729-816bca00-ef05-11e8-8988-0143b1a634e3.jpg)

In the end, the actual working _layer_ on top, say the _wallet layer_, has no restrictions on the effects. Chaos! We don't want inheritance, we want composition! That was the promise.
Well, we can fix this. The price is hard-to-read type errors if you miss something, but it's better then the alternative.
So we can simply use `Rank2Types` extension and use a layer that has the constraints defined *per function*:
```
data LoggingLayer = LoggingLayer
    { llLogDebug   :: forall m. (MonadIO m) => Text -> m ()
    , llLogInfo    :: forall m. (MonadIO m) => Text -> m ()
    , llLockNonIO  :: forall m. (MonadThrow m) => m ()
    }
```

And now, we don't have these issues.

Are we done now? YES!

