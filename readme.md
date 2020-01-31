Pure Kotlin implementation of BigInteger

GNU Classpath's BigInteger converted to Kotlin and with all java dependencies removed so it can be used with JS target.

Unsupported features:

- Serialization/deserialization
- Native code improvements/JVM intrinsics

Implementation details

- BigInteger implements `kotlin.Number`, not `java.lang.Number`
- `kotlin.random.Random` is used instead of `java.util.Random`
- Explicit import for `kotlin.text.StringBuilder` to allow use of platform specific implementation

Not working:

GNU Classpath BigInteger implementation matches Java 1.2 spec, so nothing newer is supported, for example
`BigInteger.longValueExact` and `BigInteger.sqrt`.

Support for 1.5 is inconsistent, for example `BigInteger.TEN` is supported, but `BigInteger.nextProbablePrime()` is not. 

Tests are failing for:

- modExp tests are flaky, but they are the same even for original Java version of Classpath's BigInteger
    
String conversions are extremely slow, but work.
     