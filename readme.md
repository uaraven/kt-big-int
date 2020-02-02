# Pure Kotlin implementation of BigInteger

GNU Classpath's BigInteger converted to Kotlin and with all Java dependencies removed so it can be used with JS target.

This code is a direct conversion from GNU Classpath Java source code. That means it is licensed under GPL v2 with 
Classpath extension. Please see [LICENSE](LICENSE) and [COPYING](COPYING) files for more details. 

**Implementation details**

- BigInteger implements `kotlin.Number`, not `java.lang.Number`, that means `.toInt()` instead of `.intValue()`, etc.
- `kotlin.random.Random` is used instead of `java.util.Random`
- Explicit import for `kotlin.text.StringBuilder` to allow use of platform specific implementation

**Limitations**

GNU Classpath BigInteger implementation matches Java 1.2 spec, so in general nothing newer is supported, for example
`BigInteger.longValueExact()` and `BigInteger.sqrt()`.

Support for Java 1.5 is inconsistent, for example `BigInteger.TEN` is supported, but `BigInteger.nextProbablePrime()` is not. 

**Unsupported features**

- Serialization/deserialization
- Native code improvements/JVM intrinsics

**Gotchas**

- modExp tests are flaky, but they are the same even for original Java version of Classpath's BigInteger\
  I updated one test case so it is passing now, but I am not sure how it is supposed to work as it fails with Java 13.
    
String conversions are extremely slow, but work.
     
     
**Lessons learnt**

IDEA's Java-to-Kotlin translator does good job but it screws up bitwise operations, probably because in Kotlin
they are implemented as extension methods with infix notation. 

    a = b | c + d   // in Java
    a = b | (c + d) // how it is evaluated in Java
    a = b or c + d  // in Kotlin
    a = b.or(c) + d // and how it is evaluated in Kotlin 

Best solution is to replace all infix operators with explicit method calls.
