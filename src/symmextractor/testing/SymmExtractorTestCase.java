package src.symmextractor.testing;

import java.io.IOException;

import src.TopSpin;
import src.etch.testing.EtchTestCase;
import src.etch.testing.EtchTestOutcome;
import src.promela.lexer.LexerException;
import src.promela.parser.ParserException;
import src.symmextractor.SymmExtractor;
import src.testing.SystemErrorTestOutcome;
import src.testing.TestCase;
import src.testing.TestOutcome;
import src.utilities.AbsentConfigurationFileException;
import src.utilities.BadConfigurationFileException;
import src.utilities.Config;

public class SymmExtractorTestCase extends TestCase {

	protected String foldername;

	public SymmExtractorTestCase(String foldername, String modelFilename, TestOutcome expectedOutcome) {

		super(foldername + modelFilename, expectedOutcome);
		this.foldername = foldername;
	
	}

	@Override
	public void run() {

		Config.initialiseCommandLineSwitches();

		try {

			EtchTestCase etchTest = new EtchTestCase(filename, EtchTestOutcome.WellTyped);

			etchTest.run();

			
			if(!etchTest.isPass()) {
				actualOutcome = etchTest.getOutcome();
			} else {
			
				Config.readConfigFile("symmextractor_common_config.txt", true, false);

				Config.readConfigFile(foldername + "config.txt", false, true);

				SymmExtractor extractor = new SymmExtractor(filename);
	
				TopSpin.doAutomaticSymmetryDetection(filename, extractor);
				
				if(!extractor.isWellTyped()) {
					actualOutcome = SymmExtractorFailTestOutcome.BreaksRestrictions;
				} else if(!extractor.obeysSymmetryRestrictions) {
					actualOutcome = SymmExtractorFailTestOutcome.BreaksRestrictions;
				} else {
					actualOutcome = new SymmExtractorRunTestOutcome(true, extractor.getSizeOfGroup(), extractor.requiredCosetSearch());
				}
			}

		} catch(IOException e) {
			
			actualOutcome = SystemErrorTestOutcome.IOError;
			
		} catch (InterruptedException e) {

			actualOutcome = SystemErrorTestOutcome.InterruptedError;

		} catch (BadConfigurationFileException e) {

			actualOutcome = SystemErrorTestOutcome.BadConfigurationFile;

		} catch (AbsentConfigurationFileException e) {

			actualOutcome = SystemErrorTestOutcome.NoConfigurationFileFound;

		} catch (ParserException e) {

			actualOutcome = EtchTestOutcome.ParserError;

		} catch (LexerException e) {

			actualOutcome = EtchTestOutcome.ParserError;

		}
		
	}

}
