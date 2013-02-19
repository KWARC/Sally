package info.kwarc.sally.jedit;

import java.util.List;

import info.kwarc.sally.core.SallyActionAcceptor;
import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.core.SallyManager;
import info.kwarc.sally.core.SallyService;
import sally.FileContents;
import sally.FileRef;
import sally.TextFileNotifications;
import sally.TextNotification;
import sally.TextPosition;

public class SallyJEditService {
	ITextBuffer buffer;
	SallyInteraction interaction;
	FileRef f;
	
	public SallyJEditService(ITextBuffer buffer, SallyInteraction interaction) {
		this.buffer = buffer;
		this.interaction = interaction;
		f = FileRef.newBuilder().setMime("text/stex").setResourceURI(buffer.getPath()).build();
	}
	
	boolean canHandleFile(FileRef f) {
		return f.getResourceURI().equals(buffer.getPath());
	}

	@SallyService(channel="/get")
	public void GetContents(FileRef f, SallyActionAcceptor acceptor, SallyContext context) {
		if (!canHandleFile(f))
			return;
		acceptor.acceptResult(FileContents.newBuilder().setContents(buffer.getText()).setFile(f).build());
	}
	
	@SallyService
	public void ShowMarkers(TextFileNotifications notifications, SallyActionAcceptor acceptor, SallyContext context) {
		if (!canHandleFile(notifications.getFile()))
			return;
		String resourceURI = notifications.getFile().getResourceURI();
		
		for (TextNotification notification : notifications.getNotificationsList()) {
			TextPosition position = notification.getPos();
			if (!resourceURI.equals(buffer.getPath())) {
				return;
			}
			buffer.addMarker(position.getLine(), notification.getMessage());
		}
	}
	
	public void updateMarkers() {
		List<TextNotification> notifications = interaction.getPossibleInteractions("/get/semantics", f, TextNotification.class);
		
	}
}
