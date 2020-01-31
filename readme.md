Pure Kotlin implementation of BigInteger

GNU Classpath's BigInteger converted to Kotlin and with all java dependencies removed so it can be used with JS target.

Unsupported features:

- Serialization/deserialization
- Native code improvements/JVM intrinsics
- BigInteger implements kotlin.Number, not java.lang.Number

Not working:

GNU Classpath BigInteger implementation matches Java 1.2 spec, so nothing newer is supported.

Tests are failing for:
    - array conversion
    - modExp operations
    
String conversions are extremely slow, but work
     