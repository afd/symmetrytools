package src.utilities;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

public class ErrorStreamHandler extends Thread {

	private Process p;
	private String messageHeader;
	private String messageFinaliser;
	
	public ErrorStreamHandler(Process p, String messageHeader, String messageFinaliser) {
		this.p = p;
		this.messageHeader = messageHeader;
		this.messageFinaliser = messageFinaliser;

	}

	public void run() {
		if(p!=null) {
			try {
				BufferedReader br = new BufferedReader(new InputStreamReader(p.getErrorStream()));
				String line = null;
				while((line = br.readLine())!=null) {
					System.out.println(messageHeader);
					System.out.println(line);
					while(br.ready()) {
						System.out.println(br.readLine());
					}
					System.out.println(messageFinaliser);
					
					if(p!=null) {
						p.destroy();
						p.waitFor();
					}
					System.exit(1);
				}
			} catch (IOException ioe) {
				ioe.printStackTrace();
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
	}
}
