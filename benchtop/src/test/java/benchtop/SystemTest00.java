package benchtop;

import benchtop.spi.RandoopConfiguration;
import com.google.common.io.Files;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;

import java.io.File;

import static org.junit.Assert.fail;

/**
 * @author Huascar Sanchez
 */
public class SystemTest00 {

  private static final File DIR = RandoopConfiguration.randoopOutput();

  private static File compiledTempFolder;

  @BeforeClass public static void setup() throws Exception {
    compiledTempFolder = Files.createTempDir();

    Tests.testSetup(compiledTempFolder);
  }


  @Test public void testDynamicallyCreatedClass() {
    try {
      consumesExecutionBundle(false);
    } catch (Exception e){
      fail("Failed due to : " + e.getLocalizedMessage());
    }
  }

  @Test public void testDynamicallyCreatedAndTransformedClass(){
    try {
      consumesExecutionBundle(true);
    } catch (Exception e){
      fail("Failed due to : " + e.getLocalizedMessage());
    }
  }


  private static void consumesExecutionBundle(final boolean withTransformations) throws Exception {
    Benchtop.consumes(new ExecutionBundle() {
      @Override public void configure(Environment host) {
        host.bundleTarget(compiledTempFolder);
        host.bundleOutput(DIR);
        host.bundleClasspath();
        host.bundleFocus("Regression");
        if(withTransformations) host.bundleTransformations();
      }
    });
  }


  @AfterClass public static void tearDown() throws Exception {
    Tests.testTeardown(compiledTempFolder);

    compiledTempFolder = null;
  }

}
