package typeSystem;

import static org.junit.jupiter.api.Assertions.assertThrows;

import java.util.List;

import org.junit.jupiter.api.Test;

import core.FearlessException;

class GenericCapabilityAliasTest extends testUtils.FearlessTestBase{
  private static final String cellAndBox= """
    Cell:{ read .get:base.Nat; mut .set(value:base.Nat):base.Void; }
    Box[X:imm,mut]:{ mut .get:X; }
    Boxes:{ #(cell:mut Cell):mut Box[mut Cell] ->
      mut Box[mut Cell]{ mut .get -> cell; }
    }
    """;

  @Test void mutableBoxCanReturnCapturedMutableCell(){ typeOk(List.of(cellAndBox + """
    User:{ .get(cell:mut Cell):mut Cell->(Boxes#cell).get; }
    """)); }

  @Test void rejectsDirectMutableToImmutableAlias(){
    assertThrows(FearlessException.class, () -> typeOk(List.of(cellAndBox + """
      User:{ .freeze(cell:mut Cell):imm Cell->cell; }
      """)));
  }

  @Test void rejectsImmutableAliasToCapturedMutableCell(){
    // The box captures the original cell. It does not create a fresh one.
    // .observe mutates that original while the immutable alias remains live.
    assertThrows(FearlessException.class, () -> typeOk(List.of(cellAndBox + """
      User:{
        .freeze(box:mut Box[mut Cell]):mut Box[imm Cell]->box;
        .observe(frozen:imm Cell, original:mut Cell):base.Nat->
          base.Block#(original.set(1), frozen.get);
        .breakSoundness(cell:mut Cell):base.Nat->
          this.observe(this.freeze(Boxes#cell).get, cell);
      }
      """)));
  }
}
