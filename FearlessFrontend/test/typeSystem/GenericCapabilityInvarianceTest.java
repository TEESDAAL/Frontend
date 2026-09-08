package typeSystem;

import static org.junit.jupiter.api.Assertions.assertThrows;

import java.util.List;

import org.junit.jupiter.api.Test;

import core.FearlessException;

class GenericCapabilityInvarianceTest extends testUtils.FearlessTestBase{
  @Test void preservesMutableTypeArgument(){ typeOk(List.of("""
    Cell:{}
    Box[X:imm,mut]:{ .get:X; }
    User:{ .same(box:Box[mut Cell]):Box[mut Cell]->box; }
    """)); }

  @Test void preservesImmutableTypeArgument(){ typeOk(List.of("""
    Cell:{}
    Box[X:imm,mut]:{ .get:X; }
    User:{ .same(box:Box[imm Cell]):Box[imm Cell]->box; }
    """)); }

  @Test void rejectsChangingMutableTypeArgumentToImmutable(){
    // Accepting this method lets callers retrieve a mutable Cell as immutable.
    assertThrows(FearlessException.class, () -> typeOk(List.of("""
      Cell:{}
      Box[X:imm,mut]:{ .get:X; }
      User:{ .freeze(box:Box[mut Cell]):Box[imm Cell]->box; }
      """)));
  }
}
