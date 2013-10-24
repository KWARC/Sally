package info.kwarc.sally.core.interfaces;

import info.kwarc.sally.core.theo.Coordinates;

public interface IPositionProvider {
	Coordinates getRecommendedPosition();
	void setRecommendedCoordinates(Coordinates pos);
}
