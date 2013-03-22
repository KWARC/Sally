package info.kwarc.sally.jedit;

import info.kwarc.sally.core.SallyActionAcceptor;
import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.core.SallyService;

import java.util.List;

import sally.FileContents;
import sally.FileRef;
import sally.TextFileNotifications;
import sally.TextNotification;
import sally.TextPosition;

public class SallyJEditService implements Runnable {
	ITextBuffer buffer;
	SallyInteraction interaction;
	FileRef f;
	
	public SallyJEditService(ITextBuffer buffer, SallyInteraction interaction) {
		this.buffer = buffer;
		this.interaction = interaction;
		f = FileRef.newBuilder().setMime("application/stex").setResourceURI(buffer.getPath()).build();
		buffer.addOnChangeListener(this);
		updateMarkers();
	}

	// This is the onChangeEvent
	public void run() {
		updateMarkers();
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
	
	public void showMarkers(TextFileNotifications notifications) {
		if (!canHandleFile(notifications.getFile()))
			return;
		String resourceURI = notifications.getFile().getResourceURI();
		
		for (TextNotification notification : notifications.getNotificationsList()) {
			TextPosition position = notification.getPos();
			if (!resourceURI.equals(buffer.getPath())) {
				return;
			}
			buffer.addMarker(position.getLine(), notification.getMsg());
		}
	}
	
	public void updateMarkers() {
		buffer.removeAllMarkers();
		List<TextNotification> notifications = interaction.getPossibleInteractions("/get/semantics", f, TextNotification.class);
		
		showMarkers(TextFileNotifications.newBuilder().setFile(f).addAllNotifications(notifications).build());
	}
}
